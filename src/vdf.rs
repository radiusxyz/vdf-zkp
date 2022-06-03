use bignat::nat_to_limbs;
use bignat::BigNat;
use f_to_nat;
use group::{RsaGroup, SemiGroup};
use mimc;
use num_bigint::BigUint;
use rand::thread_rng;
use sapling_crypto::bellman::groth16;
use sapling_crypto::bellman::groth16::{create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Parameters, Proof};
use sapling_crypto::bellman::pairing::ff::Field;
use sapling_crypto::bellman::pairing::ff::PrimeField;
use sapling_crypto::bellman::pairing::ff::ScalarEngine;
use sapling_crypto::bellman::{pairing::Engine, Circuit, ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num::AllocatedNum;
use std::fs;
use std::path::Path;
use std::str::FromStr;
use OptionExt;
extern crate serde;
use self::serde::{Deserialize, Serialize};
use sapling_crypto::bellman::pairing::ff::from_hex;
use sapling_crypto::bellman::pairing::ff::to_hex;

const DATA_PATH: &str = "/data";
const SNARK_PARAMETER_FILE_PATH: &str = "/vdf_zkp_snark_parameter.data";
const VDF_PARAMETER_FILE_PATH: &str = "/vdf_zkp_vdf_parameter.data";

const BASE: &str = "2";
const N: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";

macro_rules! init_big_uint_from_str {
  ($var:ident, $val:expr) => {
    let $var = BigUint::from_str($val).unwrap();
  };
}

#[derive(Debug)]
pub struct VdfInput<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  pub g_s_two_t: BigUint,
  pub g_s_two_t_plus_one: BigUint,
  pub commitment: E::Fr,
}

impl<E> VdfInput<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  pub fn new(commitment: &str, _g_s_two_t: &str, _g_s_two_t_plus_one: &str) -> Self {
    init_big_uint_from_str!(g_s_two_t, _g_s_two_t);
    init_big_uint_from_str!(g_s_two_t_plus_one, _g_s_two_t_plus_one);
    let commitment = from_hex(commitment).unwrap();

    VdfInput { commitment, g_s_two_t, g_s_two_t_plus_one }
  }
}

#[derive(Serialize, Deserialize, Clone)]
pub struct VdfParam {
  pub t: u32,
  pub g: String,
  pub g_two_t: String,
  pub g_two_t_plus_one: String,

  pub n: String,
  pub base: String,

  pub word_size: usize,
  pub word_count: usize,
}

#[derive(Serialize, Deserialize)]
pub struct SigmaProof {
  pub r1: String,
  pub r3: String,
  pub s1: String,
  pub s3: String,
  pub k: String,
}

pub struct VdfProof<E: Engine> {
  pub snark_proof: Proof<E>,
  pub sigma_proof: SigmaProof,
}

impl<E> VdfProof<E>
where
  E: Engine,
{
  pub fn new(r1: &str, r3: &str, s1: &str, s3: &str, k: &str, vdf_snark_proof_vector: Vec<u8>) -> VdfProof<E> {
    VdfProof {
      snark_proof: groth16::Proof::read(&vdf_snark_proof_vector[..]).unwrap(),
      sigma_proof: SigmaProof {
        r1: r1.to_string(),
        r3: r3.to_string(),
        s1: s1.to_string(),
        s3: s3.to_string(),
        k: k.to_string(),
      },
    }
  }
}

pub struct VdfCircuit<E>
where
  E: Engine,
{
  pub inputs: Option<VdfInput<E>>,
  pub params: VdfParam,
}

impl<E> Circuit<E> for VdfCircuit<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
    init_big_uint_from_str!(n, self.params.n.as_str());

    let g_s_two_t = BigNat::alloc_from_nat(cs.namespace(|| "g^{s*2^t}"), || Ok(self.inputs.as_ref().grab()?.g_s_two_t.clone()), self.params.word_size, self.params.word_count)?;
    let g_s_two_t_plus_one = BigNat::alloc_from_nat(cs.namespace(|| "g^{s*2^{t+1}}"), || Ok(self.inputs.as_ref().grab()?.g_s_two_t_plus_one.clone()), self.params.word_size, self.params.word_count)?;

    let n = BigNat::alloc_from_nat(cs.namespace(|| "n"), || Ok(n), self.params.word_size, self.params.word_count)?;
    let two = BigNat::alloc_from_nat(cs.namespace(|| "2"), || Ok(BigUint::from(2usize)), 2, 1)?;

    let calculated_g_s_two_t_plus_one = g_s_two_t.pow_mod(cs.namespace(|| "(g^{s*2^t})^2"), &two, &n)?;

    calculated_g_s_two_t_plus_one.equal(cs.namespace(|| "(g^{s*2^t})^2 == (g^{s*2^{t+1}})"), &g_s_two_t_plus_one)?;
    g_s_two_t_plus_one.inputize(cs.namespace(|| "g^{s*2^{t+1}}"))?;

    let y: E::Fr = E::Fr::from_str(g_s_two_t.value.clone().unwrap_or(num_bigint::BigUint::default()).to_string().as_str()).unwrap_or(E::Fr::zero());
    let allocated_y = AllocatedNum::alloc(cs.namespace(|| "Allocate y"), || Ok(y))?;
    let calculated_commitment = mimc::mimc(cs, &[allocated_y.clone(), allocated_y.clone()])?;
    let allocated_commitment = AllocatedNum::alloc(cs.namespace(|| "Allocate commitment"), || Ok(self.inputs.grab()?.commitment))?;
    let is_same_commitment = AllocatedNum::equals(cs.namespace(|| "Check commitment"), &allocated_commitment, &calculated_commitment)?;

    Boolean::enforce_equal(cs.namespace(|| "Check is_same_commitment is true"), &is_same_commitment, &Boolean::Constant(true))?;

    allocated_commitment.inputize(cs.namespace(|| "commitment"))?;
    Ok(())
  }
}

#[derive(Clone)]
pub struct VdfZKP<E>
where
  E: Engine,
{
  pub vdf_params: Option<VdfParam>,
  pub circuit_params: Option<Parameters<E>>,
}

impl<E> VdfZKP<E>
where
  E: Engine,
{
  pub fn new() -> VdfZKP<E> {
    VdfZKP { circuit_params: None, vdf_params: None }
  }

  pub fn setup_parameter(&mut self) {
    // Setup - snark parameters
    let t = 2; // TODO: Change the t value / 8388608
    let two = BigUint::from(2usize);

    let base = BigUint::from_str(BASE).unwrap();
    let n = BigUint::from_str(N).unwrap();
    let rsa_g = RsaGroup { n: n.clone(), g: base.clone() };

    let g = rsa_g.power(&base, &BigUint::from(1usize));
    let g_two_t = rsa_g.power(&base, &two.pow(t));
    let g_two_t_plus_one = rsa_g.power(&base, &two.pow(t + 1));

    self.vdf_params = Some(VdfParam {
      t,
      g: g.to_string(),
      g_two_t: g_two_t.to_string(),
      g_two_t_plus_one: g_two_t_plus_one.to_string(),
      n: N.to_string(),
      base: BASE.to_string(),
      word_size: 64,
      word_count: 32,
    });

    // Setup - circuit parameters
    let rng = &mut thread_rng();

    self.circuit_params = {
      let circuit = VdfCircuit::<E> { inputs: None, params: self.clone().vdf_params.unwrap().clone() };
      Some(generate_random_parameters(circuit, rng).unwrap())
    };
  }

  pub fn export_parameter(&self) {
    let exe = std::env::current_exe().unwrap();
    let mut data_dir_path = exe.parent().expect("Executable must be in some directory").to_str().unwrap().to_owned();
    data_dir_path.push_str(DATA_PATH);
    
    let mut snark_parameter_file_path = data_dir_path.clone();
    snark_parameter_file_path.push_str(SNARK_PARAMETER_FILE_PATH);

    let mut vdf_parameter_file_path = data_dir_path.clone();
    vdf_parameter_file_path.push_str(VDF_PARAMETER_FILE_PATH);

    if fs::create_dir_all(data_dir_path).is_ok() == false {
      return;
    };
    
    let file = std::fs::File::create(snark_parameter_file_path).expect("File creatation is failed");
    self.circuit_params.as_ref().unwrap().write(file).unwrap();

    let file = std::fs::File::create(vdf_parameter_file_path).expect("File creatation is failed");
    serde_json::to_writer(&file, &self.vdf_params).unwrap();
  }

  pub fn import_parameter(&mut self) {
    let exe = std::env::current_exe().unwrap();
    let mut data_dir_path = exe.parent().expect("Executable must be in some directory").to_str().unwrap().to_owned();
    data_dir_path.push_str(DATA_PATH);
    
    let mut snark_parameter_file_path = data_dir_path.clone();
    snark_parameter_file_path.push_str(SNARK_PARAMETER_FILE_PATH);

    let mut vdf_parameter_file_path = data_dir_path.clone();
    vdf_parameter_file_path.push_str(VDF_PARAMETER_FILE_PATH);

    if Path::new(&snark_parameter_file_path.as_str()).exists() == false {
      println!("Not exist file.");
      self.setup_parameter();
      self.export_parameter();
      return;
    }

    let file = std::fs::File::open(vdf_parameter_file_path).expect("File creatation is failed");
    self.vdf_params = serde_json::from_reader(&file).unwrap();

    let file = std::fs::File::open(snark_parameter_file_path).expect("File not found");
    self.circuit_params = Some(Parameters::read(file, false).unwrap());
  }

  pub fn generate_proof(&self, commitment: E::Fr, _s: &str) -> VdfProof<E> {
    let vdf_params = self.clone().vdf_params.unwrap();
    init_big_uint_from_str!(s, _s);
    init_big_uint_from_str!(g, vdf_params.g.as_str());
    init_big_uint_from_str!(g_two_t, vdf_params.g_two_t.as_str());
    init_big_uint_from_str!(g_two_t_plus_one, vdf_params.g_two_t_plus_one.as_str());
    init_big_uint_from_str!(n, vdf_params.n.as_str());
    init_big_uint_from_str!(base, vdf_params.base.as_str());

    let rsa_g = RsaGroup { n: n.clone(), g: base.clone() };
    let rng = &mut thread_rng();

    // 1. choose random r from F
    let r: u128 = fastrand::u128(..);
    let r = BigUint::from(r);

    // 2. R_1 <- g^r ; R_3 <- (g^(2^(T+1)))^r
    let r1 = rsa_g.power(&g, &r);
    let r3 = rsa_g.power(&g_two_t_plus_one, &r);

    // 3. c <- H(R_1, R_3) ; k <- r + c * s
    let r1_fileld = E::Fr::from_str(r1.to_string().as_str()).unwrap();
    let r3_fileld = E::Fr::from_str(r3.to_string().as_str()).unwrap();
    let c_fileld: E::Fr = mimc::helper::mimc(&[r1_fileld, r3_fileld]);
    let c = f_to_nat(&c_fileld);
    let k = r + c.clone() * s.clone();

    // 4. S_1 <- g^s ; S_2 <- (g^(2^T))^s ; S_3 <- (g^(2^(T+1)))^s
    // ** S_1 is an encryption key
    let s1 = rsa_g.power(&g, &s);
    let s2 = rsa_g.power(&g_two_t, &s);
    let s3 = rsa_g.power(&g_two_t_plus_one, &s);

    let circuit = VdfCircuit::<E> {
      inputs: Some(VdfInput::new(to_hex(&commitment).as_str(), s2.to_string().as_str(), s3.to_string().as_str())),
      params: vdf_params.clone(),
    };

    VdfProof {
      snark_proof: create_random_proof(circuit, self.circuit_params.as_ref().unwrap(), rng).unwrap(),
      sigma_proof: SigmaProof {
        r1: r1.to_string(),
        r3: r3.to_string(),
        s1: s1.to_string(),
        s3: s3.to_string(),
        k: k.to_string(),
      },
    }
  }

  pub fn verify(&self, commitment: E::Fr, proof: VdfProof<E>) -> bool {
    // Verify sigma
    // 0. parse proof -> R_1, R_3, S_1, S_3, k
    let vdf_params = self.clone().vdf_params.unwrap();
    let sigma_proof = proof.sigma_proof;
    init_big_uint_from_str!(r1, sigma_proof.r1.as_str());
    init_big_uint_from_str!(r3, sigma_proof.r3.as_str());
    init_big_uint_from_str!(s1, sigma_proof.s1.as_str());
    init_big_uint_from_str!(s3, sigma_proof.s3.as_str());
    init_big_uint_from_str!(k, sigma_proof.k.as_str());

    init_big_uint_from_str!(g, vdf_params.g.as_str());
    init_big_uint_from_str!(g_two_t_plus_one, vdf_params.g_two_t_plus_one.as_str());

    init_big_uint_from_str!(n, vdf_params.n.as_str());
    init_big_uint_from_str!(base, vdf_params.base.as_str());

    let rsa_g = RsaGroup { n: n.clone(), g: base.clone() };

    let r1_fileld = E::Fr::from_str(r1.to_string().as_str()).unwrap();
    let r3_fileld = E::Fr::from_str(r3.to_string().as_str()).unwrap();
    let c_fileld: E::Fr = mimc::helper::mimc(&[r1_fileld, r3_fileld]);
    let c = f_to_nat(&c_fileld);

    // 2. g_k <- R_1 * S_1^c ; (g_(2^(T+1)))^k = R_3 * S_3^c
    let s1_c = rsa_g.power(&s1, &c);
    let g_k_out = (s1_c * r1) % n.clone();
    let g_k = rsa_g.power(&g, &k);

    let s3_c = rsa_g.power(&s3, &n);
    let g_t_plus_one_k_out = (s3_c * r3) % n;
    let g_one_k = rsa_g.power(&g_two_t_plus_one, &k);

    if (g_one_k == g_t_plus_one_k_out) && (g_k == g_k_out) == false {
      return false;
    }

    // Verify snark
    let pvk = prepare_verifying_key(&self.circuit_params.as_ref().unwrap().vk);

    let mut inputs: Vec<<E as ScalarEngine>::Fr> = nat_to_limbs::<<E as ScalarEngine>::Fr>(&s3, vdf_params.word_size, vdf_params.word_count);
    inputs.extend([commitment]);

    verify_proof(&pvk, &proof.snark_proof, &inputs).unwrap()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use nat_to_f;
  use sapling_crypto::bellman::pairing::bls12_381::Bls12;
  use sapling_crypto::bellman::pairing::ff::from_hex;
  use sapling_crypto::bellman::pairing::ff::to_hex;
  use std::time::Instant;

  #[test]
  fn gadget_test_with_setup_parameter() {
    let mut vdf_zkp = VdfZKP::<Bls12>::new();
    vdf_zkp.setup_parameter();
    let vdf_params = vdf_zkp.clone().vdf_params.unwrap();

    println!("g: {:?}", vdf_params.g);
    println!("g_two_t: {:?}", vdf_params.g_two_t);
    println!("g_two_t_plus_one: {:?}", vdf_params.g_two_t_plus_one);

    let start = Instant::now();
    let duration = start.elapsed();
    println!("Setup {:?}", duration);

    vdf_zkp.export_parameter();

    let s: u128 = fastrand::u128(..);
    let s = BigUint::from(s);

    init_big_uint_from_str!(g_two_t, vdf_params.g_two_t.as_str());
    init_big_uint_from_str!(n, vdf_params.n.as_str());

    let s2 = g_two_t.modpow(&s, &n);
    let s2_field = nat_to_f::<<Bls12 as ScalarEngine>::Fr>(&s2).unwrap();
    let commitment = mimc::helper::mimc(&[s2_field.clone(), s2_field.clone()]);
    let commitment_hex = to_hex(&commitment);

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(commitment, s.to_string().as_str());
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let commitment = from_hex(commitment_hex.as_str()).unwrap();

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(commitment, proof);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }

  #[test]
  fn gadget_test_with_load_parameter() {
    let mut vdf_zkp = VdfZKP::<Bls12>::new();
    vdf_zkp.import_parameter();
    let vdf_params = vdf_zkp.clone().vdf_params.unwrap();

    let s: u128 = fastrand::u128(..);
    let s = BigUint::from(s);

    init_big_uint_from_str!(g_two_t, vdf_params.g_two_t.as_str());
    init_big_uint_from_str!(n, vdf_params.n.as_str());

    let s2 = g_two_t.modpow(&s, &n);
    let s2_field = nat_to_f::<<Bls12 as ScalarEngine>::Fr>(&s2).unwrap();
    let commitment = mimc::helper::mimc(&[s2_field.clone(), s2_field.clone()]);

    let commitment_hex = to_hex(&commitment);

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(commitment, s.to_string().as_str());
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let commitment = from_hex(commitment_hex.as_str()).unwrap();

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(commitment, proof);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }
}
