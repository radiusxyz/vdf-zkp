use bignat::nat_to_limbs;
use bignat::BigNat;
use mimc;
use num_bigint::BigUint;
use poly::Polynomial;
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

const DATA_PATH: &str = "./data";
const PARAMETER_FILE_PATH: &str = "./data/vdf_zkp_parameter.data";

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
  pub two_two_t: BigUint,
  pub p_minus_one: BigUint,
  pub q_minus_one: BigUint,

  pub quotient: BigUint,
  pub remainder: BigUint,

  pub g: BigUint,
  pub y: BigUint,

  pub commitment: E::Fr,
}

impl<E> Input<E>
where
  E: Engine,
  E::Fr: PrimeField,
{
  pub fn new(commitment: E::Fr, two_two_t: BigUint, p_minus_one: BigUint, q_minus_one: BigUint, quotient: BigUint, remainder: BigUint, g: BigUint, y: BigUint) -> Self {
    Input {
      commitment,
      two_two_t,
      p_minus_one,
      q_minus_one,
      quotient,
      remainder,
      g,
      y,
    }
  }
}

#[derive(Clone)]
pub struct Param {
  pub word_size: usize,
  pub two_two_t_word_count: usize,
  pub quotient_word_count: usize,
  pub prime_word_count: usize,
  pub n_word_count: usize,
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
    let two_two_t = BigNat::alloc_from_nat(cs.namespace(|| "2^{2^t}"), || Ok(self.inputs.as_ref().grab()?.two_two_t.clone()), self.params.word_size, self.params.two_two_t_word_count)?;
    let p_minus_one = BigNat::alloc_from_nat(cs.namespace(|| "p-1"), || Ok(self.inputs.as_ref().grab()?.p_minus_one.clone()), self.params.word_size, self.params.prime_word_count)?;
    let q_minus_one = BigNat::alloc_from_nat(cs.namespace(|| "q-1"), || Ok(self.inputs.as_ref().grab()?.q_minus_one.clone()), self.params.word_size, self.params.prime_word_count)?;

    let quotient = BigNat::alloc_from_nat(cs.namespace(|| "quotient"), || Ok(self.inputs.as_ref().grab()?.quotient.clone()), self.params.word_size, self.params.quotient_word_count)?;
    let remainder = BigNat::alloc_from_nat(cs.namespace(|| "remainder"), || Ok(self.inputs.as_ref().grab()?.remainder.clone()), self.params.word_size, self.params.n_word_count)?;

    let g = BigNat::alloc_from_nat(cs.namespace(|| "g"), || Ok(self.inputs.as_ref().grab()?.g.clone()), self.params.word_size, self.params.n_word_count)?;
    let y = BigNat::alloc_from_nat(cs.namespace(|| "y"), || Ok(self.inputs.as_ref().grab()?.y.clone()), self.params.word_size, self.params.n_word_count)?;

    let one = BigNat::alloc_from_nat(cs.namespace(|| "1"), || Ok(BigUint::from(1usize)), 1, 1)?;

    let one_poly = Polynomial::from(one.clone());
    let p_minus_one_poly = Polynomial::from(p_minus_one.clone());
    let q_minus_one_poly = Polynomial::from(q_minus_one.clone());
    let quotient_poly = Polynomial::from(quotient.clone());
    let remainder_poly = Polynomial::from(remainder.clone());
    let pi_n_poly = p_minus_one_poly.alloc_product(cs.namespace(|| "(p-1)(q-1) = pi_n(totient)"), &q_minus_one_poly)?;

    let p_poly = Polynomial::from(p_minus_one_poly).sum(&one_poly);
    let q_poly = Polynomial::from(q_minus_one_poly).sum(&one_poly);
    let n_poly = p_poly.alloc_product(cs.namespace(|| "pq = n"), &q_poly)?;

    let qpi_n = quotient_poly.alloc_product(cs.namespace(|| "quotient * pi_n(totient)"), &pi_n_poly)?;
    let qpi_n_plus_remainder = Polynomial::from(qpi_n).sum(&remainder_poly);

    let max_word = BigUint::from(std::cmp::min(p_minus_one.limbs.len(), q_minus_one.limbs.len())) * &p_minus_one.params.max_word * &q_minus_one.params.max_word;
    let pi_n = BigNat::from_poly(Polynomial::from(pi_n_poly), self.params.word_size, max_word.clone()); // 1: pi&q_minus_one.params.max_word-1n
    let n = BigNat::from_poly(Polynomial::from(n_poly), self.params.word_size, max_word.clone()); // 1: n

    let max_word = BigUint::from(std::cmp::min(quotient.limbs.len(), pi_n.limbs.len())) * &quotient.params.max_word * &pi_n.params.max_word + &remainder.params.max_word;
    let qpi_n_plus_remainder_big_nat = BigNat::from_poly(Polynomial::from(qpi_n_plus_remainder), self.params.word_size, max_word);

    let gr_n = g.pow_mod(cs.namespace(|| "g^r mod n"), &remainder, &n)?;

    let expected_y: E::Fr = E::Fr::from_str(gr_n.value.clone().unwrap_or(num_bigint::BigUint::default()).to_string().as_str()).unwrap_or(E::Fr::zero());
    let allocated_expected_y = AllocatedNum::alloc(cs.namespace(|| "Allocate y"), || Ok(expected_y))?;
    
    let calculated_commitment = mimc::mimc(cs, &[allocated_expected_y.clone(), allocated_expected_y.clone()])?;

    let allocated_commitment = AllocatedNum::alloc(cs.namespace(|| "Allocate commitment"), || Ok(self.inputs.grab()?.commitment))?;
    let is_same_commitment = AllocatedNum::equals(cs.namespace(|| "Check commitment and MIMC(g^r mod n) / MIMC(y)"), &allocated_commitment, &calculated_commitment)?;

    println!("Public inputs");
    println!("two_two_t: {:?}", two_two_t.value);
    println!("g: {:?}", g.value);
    println!("n (it is calculated in the circuit): {:?}", n.value);
    println!("allocated_commitment: {:?}", allocated_commitment.get_value());
    println!("");

    println!("Private inputs");
    println!("p_minus_one: {:?}", p_minus_one.value);
    println!("q_minus_one: {:?}", q_minus_one.value);
    println!("pi_n: {:?}", pi_n.value);
    println!("quotient: {:?}", quotient.value);
    println!("remainder: {:?}", remainder.value);
    println!("y: {:?}", y.value);
    println!("calculated_commitment: {:?}", calculated_commitment.get_value());
    println!("");

    two_two_t.is_equal(cs.namespace(|| "2^{2^t} == q * pi_n + r"), &qpi_n_plus_remainder_big_nat)?;
    y.equal(cs.namespace(|| "y == g^r mod n"), &gr_n)?;
    Boolean::enforce_equal(cs.namespace(|| "commitment == MIMC(g^r mod n) MIMC(y)"), &is_same_commitment, &Boolean::Constant(true))?;

    two_two_t.inputize(cs.namespace(|| "two_two_t"))?;
    g.inputize(cs.namespace(|| "g"))?;
    n.inputize(cs.namespace(|| "n"))?;
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
    VdfZKP {
      params: None,
      vdf_param: Param {
        word_size: 64,
        two_two_t_word_count: 4,
        quotient_word_count: 2,
        n_word_count: 2,
        prime_word_count: 1,
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

  pub fn generate_proof(&self, _two_two_t: &str, _p_minus_one: &str, _q_minus_one: &str, _quotient: &str, _remainder: &str, _g: &str, _y: &str) -> Proof<E> {
    init_big_uint_from_str!(two_two_t, _two_two_t);
    init_big_uint_from_str!(p_minus_one, _p_minus_one);
    init_big_uint_from_str!(q_minus_one, _q_minus_one);
    init_big_uint_from_str!(quotient, _quotient);
    init_big_uint_from_str!(remainder, _remainder);
    init_big_uint_from_str!(g, _g);
    init_big_uint_from_str!(y, _y);

    let rng = &mut thread_rng();

    let commit = PrimeField::from_str(_y).unwrap();
    let y_commitment = mimc::helper::mimc(&[commit, commit]);
    
    let circuit = VdfCircuit::<E> {
      inputs: Some(Input::new(y_commitment, two_two_t, p_minus_one, q_minus_one, quotient, remainder, g, y)),
      params: self.vdf_param.clone(),
    };

    create_random_proof(circuit, self.params.as_ref().unwrap(), rng).unwrap()
  }

  pub fn verify(&self, proof: Proof<E>, _commitment: &str, _two_two_t: &str, _g: &str, _n: &str) -> bool {
    init_big_uint_from_str!(two_two_t, _two_two_t);
    init_big_uint_from_str!(g, _g);
    init_big_uint_from_str!(n, _n);

    let pvk = prepare_verifying_key(&self.params.as_ref().unwrap().vk);

    let commitment = from_hex::<<E as ScalarEngine>::Fr>(_commitment).unwrap();

    let mut inputs: Vec<<E as ScalarEngine>::Fr> = nat_to_limbs::<<E as ScalarEngine>::Fr>(&two_two_t, self.vdf_param.word_size, self.vdf_param.two_two_t_word_count);
    inputs.extend(nat_to_limbs::<<E as ScalarEngine>::Fr>(&g, self.vdf_param.word_size, self.vdf_param.n_word_count));
    inputs.extend(nat_to_limbs::<<E as ScalarEngine>::Fr>(&n, self.vdf_param.word_size, self.vdf_param.n_word_count));
    inputs.extend([commitment]);

    verify_proof(&pvk, &proof, &inputs).unwrap()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use sapling_crypto::bellman::pairing::bls12_381::Bls12;
  use sapling_crypto::bellman::pairing::ff::to_hex;
  use std::time::Instant;

  const G: &str = "2";
  const TWO_TWO_T: &str = "2";

  const P_MINUS_ONE: &str = "2";
  const Q_MINUS_ONE: &str = "4";

  const QUOTIENT: &str = "0";
  const REMAINDER: &str = "2";
  const Y: &str = "4";
  const N: &str = "15";

  #[test]
  fn gadget_test_with_setup_parameter() {
    let mut vdf_zkp = VdfZKP::<Bls12>::new();
    let start = Instant::now();
    vdf_zkp.setup_parameter();
    let duration = start.elapsed();
    println!("Setup {:?}", duration);

    vdf_zkp.export_parameter();

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(TWO_TWO_T, P_MINUS_ONE, Q_MINUS_ONE, QUOTIENT, REMAINDER, G, Y);
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let commit = <Bls12 as ScalarEngine>::Fr::from_str(Y).unwrap();
    let commitment = mimc::helper::mimc(&[commit, commit]);
    let commitment = to_hex(&commitment);

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(proof, commitment.to_string().as_str(), TWO_TWO_T, G, N);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }

  #[test]
  fn gadget_test_with_load_parameter() {
    let mut vdf_zkp = VdfZKP::<Bls12>::new();
    vdf_zkp.import_parameter();

    let start = Instant::now();
    let proof = vdf_zkp.generate_proof(TWO_TWO_T, P_MINUS_ONE, Q_MINUS_ONE, QUOTIENT, REMAINDER, G, Y);
    let duration = start.elapsed();
    println!("Create random proof {:?}", duration);

    let commit = <Bls12 as ScalarEngine>::Fr::from_str(Y).unwrap();
    let commitment = mimc::helper::mimc(&[commit, commit]);
    let commitment = to_hex(&commitment);

    let start = Instant::now();
    let is_varified = vdf_zkp.verify(proof, commitment.to_string().as_str(), TWO_TWO_T, G, N);
    let duration = start.elapsed();
    println!("Verify proof {:?} / {:?}", duration, is_varified);
  }
}