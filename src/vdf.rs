use bignat::nat_to_limbs;
use bignat::BigNat;
use mimc;
use num_bigint::BigUint;
use rand::thread_rng;
use sapling_crypto::bellman::groth16::{create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Parameters, Proof};
use sapling_crypto::bellman::pairing::ff::from_hex;
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
use group::{RsaGroup, SemiGroup};
use f_to_nat;
const DATA_PATH: &str = "./data";
const PARAMETER_FILE_PATH: &str = "./data/vdf_zkp_parameter.data";

const BASE: &str = "2";
const N: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";

macro_rules! init_big_uint_from_str {
  ($var:ident, $val:expr) => {
    let $var = BigUint::from_str($val).unwrap();
  };
}

#[derive(Debug)]
pub struct Input<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  pub g_s_two_t: BigUint,
  pub g_s_two_t_plus_one: BigUint,

  pub commitment: E::Fr,
}

impl<E> Input<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  pub fn new(commitment: E::Fr, g_s_two_t: BigUint, g_s_two_t_plus_one: BigUint) -> Self {
    Input { commitment, g_s_two_t, g_s_two_t_plus_one }
  }
}

#[derive(Clone)]
pub struct Param {
  pub word_size: usize,
  pub word_count: usize,

  pub g: BigUint,
  pub g_two_t: BigUint,
  pub g_two_t_plus_one: BigUint,

  pub n: BigUint,
  pub base: BigUint,
}

#[derive(Debug)]
pub struct SigmaProof {
  r1: BigUint,
  r3: BigUint,
  s1: BigUint,
  s3: BigUint,
  k: BigUint,
}

pub struct VdfProof<E: Engine> {
  pub snark_proof: Proof<E>,
  pub sigma_proof: SigmaProof,
}

pub struct VdfCircuit<E>
where
  E: Engine,
{
  pub inputs: Option<Input<E>>,
  pub params: Param,
}

impl<E> Circuit<E> for VdfCircuit<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
    let g_s_two_t = BigNat::alloc_from_nat(cs.namespace(|| "g^{s*2^t}"), || Ok(self.inputs.as_ref().grab()?.g_s_two_t.clone()), self.params.word_size, self.params.word_count)?;
    let g_s_two_t_plus_one = BigNat::alloc_from_nat(cs.namespace(|| "g^{s*2^{t+1}}"), || Ok(self.inputs.as_ref().grab()?.g_s_two_t_plus_one.clone()), self.params.word_size, self.params.word_count)?;

    let n = BigNat::alloc_from_nat(cs.namespace(|| "n"), || Ok(self.params.n.clone()), self.params.word_size, self.params.word_count)?;
    let two = BigNat::alloc_from_nat(cs.namespace(|| "2"), || Ok(BigUint::from(2usize)), 2, 1)?;

    let calculated_g_s_two_t_plus_one = g_s_two_t.pow_mod(cs.namespace(|| "(g^{s*2^t})^2"), &two, &n)?;
    println!("calculated_g_s_two_t_plus_one: {:?}", calculated_g_s_two_t_plus_one.value);

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

pub struct VdfZKP<E>
where
  E: Engine,
{
  vdf_param: Param,
  pub params: Option<Parameters<E>>,
}

impl<E> VdfZKP<E>
where
  E: Engine,
{
  pub fn new() -> VdfZKP<E> {
    let t = 2;
    let two_t = BigUint::from(2usize);

    let base = BigUint::from_str(BASE).unwrap();
    let n = BigUint::from_str(N).unwrap();
    let g = RsaGroup { n: n.clone(), g: base.clone() };

    VdfZKP {
      params: None,
      vdf_param: Param {
        word_size: 64,
        word_count: 32,
        g: g.power(&base, &BigUint::from(1usize)),
        g_two_t: g.power(&base, &two_t.pow(t)),
        g_two_t_plus_one: g.power(&base, &two_t.pow(t + 1)),
        n,
        base,
      },
    }
  }

  pub fn setup_parameter(&mut self) {
    let rng = &mut thread_rng();

    self.params = {
      let circuit = VdfCircuit::<E> { inputs: None, params: self.vdf_param.clone() };
      Some(generate_random_parameters(circuit, rng).unwrap())
    };
  }

  pub fn export_parameter(&self) {
    if fs::create_dir_all(DATA_PATH).is_ok() == false {
      return;
    };
    let file = std::fs::File::create(PARAMETER_FILE_PATH).expect("File creatation is failed");
    self.params.as_ref().unwrap().write(file).unwrap();
  }

  pub fn import_parameter(&mut self) {
    if Path::new(PARAMETER_FILE_PATH).exists() == false {
      println!("Not exist file.");
      self.setup_parameter();
      self.export_parameter();
      return;
    }

    let file = std::fs::File::open(PARAMETER_FILE_PATH).expect("File not found");
    self.params = Some(Parameters::read(file, false).unwrap());
  }

  pub fn generate_proof(&self, _g_s_two_t: &str) -> VdfProof<E> {
    init_big_uint_from_str!(g_s_two_t, _g_s_two_t);

    let rsa_g = RsaGroup { n: self.vdf_param.n.clone(), g: self.vdf_param.base.clone() };
    let rng = &mut thread_rng();

    // 1. choose random s,r from F
    let s: u128 = fastrand::u128(..);
    let r: u128 = fastrand::u128(..);

    let s = BigUint::from(s);
    let r = BigUint::from(r);
    println!("1.choose random s, r :{} ,{}", s, r);

    // 2. R_1 <- g^r ; R_3 <- (g^(2^(T+1)))^r
    let r1 = rsa_g.power(&self.vdf_param.g, &r);
    let r3 = rsa_g.power(&self.vdf_param.g_two_t_plus_one, &r);
    println!("2. R_1, R_3 : {:?} , {:?}", r1, r3);

    // 3. c <- H(R_1, R_3) ; k <- r + c * s
    let r1_fileld = E::Fr::from_str(r1.to_string().as_str()).unwrap();
    let r3_fileld = E::Fr::from_str(r3.to_string().as_str()).unwrap();
    let c_fileld: E::Fr = mimc::helper::mimc(&[r1_fileld, r3_fileld]);
    let c = f_to_nat(&c_fileld);
    let k = r + c.clone() * s.clone();
    println!("3. c, k : {}, {}", c, k);

    // 4. S_1 <- g^s ; S_2 <- (g^(2^T))^s ; S_3 <- (g^(2^(T+1)))^s
    // ** S_1 is an encryption key
    let s1 = rsa_g.power(&self.vdf_param.g, &s);
    let s2 = rsa_g.power(&self.vdf_param.g_two_t, &s);
    let s3 = rsa_g.power(&self.vdf_param.g_two_t_plus_one, &s);
    println!("4. s1, s_2, s3 : {} , {} , {}", s1, s2, s3);

    let commit = PrimeField::from_str(_g_s_two_t).unwrap();
    let commitment = mimc::helper::mimc(&[commit, commit]);
    let two = BigUint::from(2usize);
    let g_s_two_t_plus_one = rsa_g.power(&g_s_two_t, &two);
    println!("5. g_s_two_t_plus_one : {}", g_s_two_t_plus_one);

    let circuit = VdfCircuit::<E> {
      inputs: Some(Input::new(commitment, g_s_two_t, g_s_two_t_plus_one)),
      params: self.vdf_param.clone(),
    };
    VdfProof {
      snark_proof: create_random_proof(circuit, self.params.as_ref().unwrap(), rng).unwrap(),
      sigma_proof: SigmaProof { r1, r3, s1, s3, k },
    }
  }

  pub fn verify(&self, proof: VdfProof<E>, _commitment: &str, _g_s_two_t_plus_one: &str) -> bool {
    // Verify sigma
    // 0. parse proof -> R_1, R_3, S_1, S_3, k
    let sigma_proof = proof.sigma_proof;
    let rsa_g = RsaGroup { n: self.vdf_param.n.clone(), g: self.vdf_param.base.clone() };
    let n = self.vdf_param.n.clone();
    let r1 = sigma_proof.r1;
    let r3 = sigma_proof.r3;
    let s1 = sigma_proof.s1;
    let s3 = sigma_proof.s3;
    let k = sigma_proof.k;

    let r1_fileld = E::Fr::from_str(r1.to_string().as_str()).unwrap();
    let r3_fileld = E::Fr::from_str(r3.to_string().as_str()).unwrap();
    let c_fileld: E::Fr = mimc::helper::mimc(&[r1_fileld, r3_fileld]);
    let c = f_to_nat(&c_fileld);

    // 2. g_k <- R_1 * S_1^c ; (g_(2^(T+1)))^k = R_3 * S_3^c
    let s1_c = rsa_g.power(&s1, &c);
    let g_k_out = (s1_c * r1) % n.clone();
    let g_k = rsa_g.power(&self.vdf_param.g, &k);
    println!("g_k : {}", g_k);
    println!("g_k_out : {}", g_k_out);

    let s3_c = rsa_g.power(&s3, &n);

    let g_t_plus_one_k_out = (s3_c * r3) % n;
    let g_one_k = rsa_g.power(&self.vdf_param.g_two_t_plus_one, &k);
    println!("g_k : {}", g_one_k);
    println!("g_t_plus_one :{}", g_t_plus_one_k_out);

    if (g_one_k == g_t_plus_one_k_out) && (g_k == g_k_out) == false {
      return false;
    }

    // Verify snark
    init_big_uint_from_str!(g_s_two_t_plus_one, _g_s_two_t_plus_one);
    let pvk = prepare_verifying_key(&self.params.as_ref().unwrap().vk);

    let commitment = from_hex::<<E as ScalarEngine>::Fr>(_commitment).unwrap();

    let mut inputs: Vec<<E as ScalarEngine>::Fr> = nat_to_limbs::<<E as ScalarEngine>::Fr>(&g_s_two_t_plus_one, self.vdf_param.word_size, self.vdf_param.word_count);
    inputs.extend([commitment]);

    verify_proof(&pvk, &proof.snark_proof, &inputs).unwrap()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use sapling_crypto::bellman::pairing::bls12_381::Bls12;
  use sapling_crypto::bellman::pairing::ff::to_hex;
  use std::time::Instant;

  const Y: &str = "4";
  const G_S_TWO_T_PLUS_ONE: &str = "16";

  #[test]
  fn gadget_test_with_setup_parameter() {
    let mut vdf_zkp = VdfZKP::<Bls12>::new();
    println!("g: {:?}", vdf_zkp.vdf_param.g);
    println!("g_two_t: {:?}", vdf_zkp.vdf_param.g_two_t);
    println!("g_two_t_plus_one: {:?}", vdf_zkp.vdf_param.g_two_t_plus_one);

    let start = Instant::now();
    vdf_zkp.setup_parameter();
    let duration = start.elapsed();
    println!("Setup {:?}", duration);

    vdf_zkp.export_parameter();

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(Y);
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let commit = <Bls12 as ScalarEngine>::Fr::from_str(Y).unwrap();
    let commitment = mimc::helper::mimc(&[commit, commit]);
    let commitment = to_hex(&commitment);

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(proof, commitment.to_string().as_str(), G_S_TWO_T_PLUS_ONE);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }

  #[test]
  fn gadget_test_with_load_parameter() {
    let mut vdf_zkp = VdfZKP::<Bls12>::new();
    vdf_zkp.import_parameter();

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(Y);
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let commit = <Bls12 as ScalarEngine>::Fr::from_str(Y).unwrap();
    let commitment = mimc::helper::mimc(&[commit, commit]);
    let commitment = to_hex(&commitment);

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(proof, commitment.to_string().as_str(), G_S_TWO_T_PLUS_ONE);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }
}
