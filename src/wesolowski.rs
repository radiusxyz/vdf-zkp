use num_bigint::BigUint;
use num_traits::One;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};

use bignat::BigNat;
use gadget::Gadget;
use group::{CircuitSemiGroup, SemiGroup};
use OptionExt;

/// Computes `b ^ (prod(xs) / l) % m`, cleverly.
pub fn base_to_product<'a, G: SemiGroup, I: Iterator<Item = &'a BigUint>>(g: &G, b: &G::Elem, l: &BigUint, xs: I) -> G::Elem {
  base_to_product_helper(g, &BigUint::one(), b, l, xs).0
}

/// Computes `b ^ (a * prod(xs) / l) % m` and `b ^ prod(x) % m`.
pub fn base_to_product_helper<'a, G: SemiGroup, I: Iterator<Item = &'a BigUint>>(g: &G, a: &BigUint, b: &G::Elem, l: &BigUint, mut xs: I) -> (G::Elem, G::Elem) {
  if let Some(x) = xs.next() {
    let (rq, rp) = base_to_product_helper(g, &(a * x % l), b, l, xs);
    (g.op(&g.power(&rp, &(a * x / l)), &rq), g.power(&rp, &x))
  } else {
    (g.power(&b, &(a / l)), b.clone())
  }
}

/// Computes `b ^ (prod(xs) / l) % m`, naively.
pub fn base_to_product_naive<'a, G: SemiGroup, I: Iterator<Item = &'a BigUint>>(g: &G, b: &G::Elem, l: &BigUint, xs: I) -> G::Elem {
  let mut pow = BigUint::one();
  for x in xs {
    pow *= x;
  }
  pow /= l;
  g.power(&b, &pow)
}

/// \exists q s.t. q^l \times base^r = result
pub fn proof_of_exp<E: Engine, G: CircuitSemiGroup<E = E>, CS: ConstraintSystem<E>>(mut cs: CS, group: &G, base: &G::Elem, power_factors: &[BigNat<E>], challenge: &BigNat<E>, result: &G::Elem) -> Result<(), SynthesisError>
where
  G::Elem: Gadget<Value = <G::Group as SemiGroup>::Elem>,
{
  let q_value: Option<<G::Group as SemiGroup>::Elem> = { group.group().and_then(|g| base.value().and_then(|b| challenge.value().and_then(|c| power_factors.iter().map(|pow| pow.value()).collect::<Option<Vec<&BigUint>>>().map(|facs| base_to_product(g, b, c, facs.into_iter()))))) };
  let r_computation = || -> Result<BigUint, SynthesisError> {
    let mut prod = BigUint::one();
    let l = challenge.value.grab()?;
    for pow in power_factors {
      if pow.params.limb_width != challenge.params.limb_width {
        return Err(SynthesisError::Unsatisfiable);
      }
      prod = prod * pow.value.grab()? % l;
    }
    Ok(prod)
  };
  let q = <G::Elem as Gadget>::alloc(cs.namespace(|| "Q"), q_value.as_ref(), base.access().clone(), <G::Elem as Gadget>::params(base))?;
  let r = BigNat::alloc_from_nat(cs.namespace(|| "r"), r_computation, challenge.params.limb_width, challenge.limbs.len())?;
  let ql = group.power(cs.namespace(|| "Q^l"), &q, &challenge)?;
  let br = group.power(cs.namespace(|| "b^r"), &base, &r)?;
  let left = group.op(cs.namespace(|| "Q^l b^r"), &ql, &br)?;
  <G::Elem as Gadget>::assert_equal(cs.namespace(|| "Q^l b^r == res"), &left, &result)
}

#[cfg(test)]
mod tests {
  use super::*;

  use quickcheck::TestResult;
  use test_helpers::*;

  use group::{CircuitRsaGroup, CircuitRsaGroupParams, RsaGroup};

  use std::str::FromStr;

  pub struct PoEInputs<'a> {
    pub b: &'a str,
    pub exps: &'a [&'a str],
    pub l: &'a str,
    pub m: &'a str,
    pub res: Option<&'a str>, // If missing, it will be computed
  }

  pub struct PoEParams {
    pub limb_width: usize,
    pub n_limbs_b: usize,
    pub n_limbs_e: usize,
  }

  pub struct PoE<'a> {
    inputs: Option<PoEInputs<'a>>,
    params: PoEParams,
  }

  circuit_tests! {
    proof_1_to_1: (PoE {
      params: PoEParams {
        limb_width: 4,
        n_limbs_b: 2,
        n_limbs_e: 1,
      },
      inputs: Some(PoEInputs {
        b: "1",
        m: "255",
        exps: &["1"],
        l: "15",
        res: Some("1"),
      }),
    }, true),
    proof_1_to_1_2_3_4_15: (PoE {
      params: PoEParams {
        limb_width: 4,
        n_limbs_b: 2,
        n_limbs_e: 1,
      },
      inputs: Some(PoEInputs {
        b: "1",
        m: "255",
        exps: &[ "1", "2", "3", "4", "15"],
        l: "15",
        res: Some("1"),
      }),
    }, true),
    proof_2_to_1_2_3_4_15_wrong: (PoE {
      params: PoEParams {
        limb_width: 4,
        n_limbs_b: 2,
        n_limbs_e: 1,
      },
      inputs: Some(PoEInputs {
        b: "2",
        m: "255",
        exps: &["1", "2", "3", "4", "15"],
        l: "15",
        res: Some("16"),
      }),
    }, false),
    proof_2_to_1_2_3_4_15: (PoE {
      params: PoEParams {
        limb_width: 4,
        n_limbs_b: 2,
        n_limbs_e: 1,
      },
      inputs: Some(PoEInputs {
        b: "2",
        m: "255",
        exps: &["1", "2", "3", "4", "15"],
        l: "15",
        res: None,
      }),
    }, true),
    proof_7_to_many_powers: (PoE {
      params: PoEParams {
        limb_width: 4,
        n_limbs_b: 2,
        n_limbs_e: 1,
      },
      inputs: Some(PoEInputs {
        b: "7",
        m: "255",
        exps: &["1", "2", "3", "4", "9", "4", "11", "15", "4", "15"],
        l: "13",
        res: None,
      }),
    }, true),
  }

  impl<'a, E: Engine> Circuit<E> for PoE<'a> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
      let b = BigNat::alloc_from_nat(cs.namespace(|| "b"), || Ok(BigUint::from_str(self.inputs.grab()?.b).unwrap()), self.params.limb_width, self.params.n_limbs_b)?;

      let exps = self
        .inputs
        .grab()?
        .exps
        .iter()
        .enumerate()
        .map(|(i, e)| BigNat::alloc_from_nat(cs.namespace(|| format!("e {}", i)), || Ok(BigUint::from_str(e).unwrap()), self.params.limb_width, self.params.n_limbs_e))
        .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;

      let res_computation = || -> Result<BigUint, SynthesisError> {
        let ref inputs = self.inputs.grab()?;
        inputs.res.map(|r| Ok(BigUint::from_str(r).unwrap())).unwrap_or_else(|| {
          let mut acc = BigUint::from_str(inputs.b).unwrap();
          let m = BigUint::from_str(inputs.m).unwrap();
          for p in inputs.exps {
            acc = acc.modpow(&BigUint::from_str(p).unwrap(), &m);
          }
          Ok(acc)
        })
      };

      let res = BigNat::alloc_from_nat(cs.namespace(|| "res"), res_computation, self.params.limb_width, self.params.n_limbs_b)?;

      let group = self.inputs.as_ref().map(|is| RsaGroup { n: BigUint::from_str(is.m).unwrap(), g: BigUint::from(2usize) });
      let g = <CircuitRsaGroup<E> as Gadget>::alloc(
        cs.namespace(|| "g"),
        group.as_ref(),
        (),
        &CircuitRsaGroupParams {
          g_word_width: self.params.n_limbs_b,
          g_word_count: self.params.limb_width,
          n_word_width: self.params.n_limbs_b,
          n_word_count: self.params.limb_width,
        },
      )?;

      let l = BigNat::alloc_from_nat(cs.namespace(|| "l"), || Ok(BigUint::from_str(self.inputs.grab()?.l).unwrap()), self.params.limb_width, self.params.n_limbs_b)?;
      proof_of_exp(cs.namespace(|| "proof of exp"), &g, &b, &exps, &l, &res)
    }
  }

  #[test]
  fn base_to_product_0() {
    let b = BigUint::from(2usize);
    let n = BigUint::from(2usize);
    let l = BigUint::from(2usize);
    let xs = [BigUint::from(1usize), BigUint::from(1usize), BigUint::from(1usize)];
    let g = RsaGroup { n, g: BigUint::from(2usize) };
    let clever = base_to_product(&g, &b, &l, xs.iter());
    assert_eq!(clever, BigUint::from(1usize));
  }

  #[test]
  fn base_to_product_1() {
    let b = BigUint::from(2usize);
    let xs = [BigUint::from(4usize), BigUint::from(3usize), BigUint::from(1usize)];
    let l = BigUint::from(3usize);
    let n = BigUint::from(3usize);
    let g = RsaGroup { n, g: BigUint::from(2usize) };
    let clever = base_to_product(&g, &b, &l, xs.iter());
    assert_eq!(clever, BigUint::from(1usize));
  }

  #[test]
  fn base_to_product_2() {
    let b = BigUint::from(2usize);
    let n = BigUint::from(17usize);
    let l = BigUint::from(2usize);
    let xs = [BigUint::from(1usize), BigUint::from(1usize), BigUint::from(1usize)];
    let g = RsaGroup { n, g: BigUint::from(2usize) };
    let clever = base_to_product(&g, &b, &l, xs.iter());
    assert_eq!(clever, BigUint::from(1usize));
  }

  #[quickcheck]
  fn qc_naive_and_clever_base_to_product_agree(b: u8, x0: u8, x1: u8, x2: u8, l: u8, n: u8) -> TestResult {
    if b < 1 {
      return TestResult::discard();
    }
    let b = BigUint::from(b);
    if n < 2 {
      return TestResult::discard();
    }
    let n = BigUint::from(n);
    if l < 2 {
      return TestResult::discard();
    }
    let l = BigUint::from(l);
    let xs = [BigUint::from(x0), BigUint::from(x1), BigUint::from(x2)];
    let g = RsaGroup { n, g: BigUint::from(2usize) };
    let clever = base_to_product(&g, &b, &l, xs.iter());
    let naive = base_to_product_naive(&g, &b, &l, xs.iter());
    TestResult::from_bool(clever == naive)
  }

  #[quickcheck]
  fn qc_proof_of_exp(b: u8, x0: u8, x1: u8, x2: u8, l: u8) -> TestResult {
    if b < 1 {
      return TestResult::discard();
    }
    if l < 2 {
      return TestResult::discard();
    }
    let b = format!("{}", b);
    let x0 = format!("{}", x0);
    let x1 = format!("{}", x1);
    let x2 = format!("{}", x2);
    let l = format!("{}", l);
    let m = "255";
    let xs: &[&str] = &[&x0, &x1, &x2];
    let circuit = PoE {
      inputs: Some(PoEInputs { b: &b, m: &m, l: &l, exps: xs, res: None }),
      params: PoEParams { limb_width: 4, n_limbs_b: 2, n_limbs_e: 2 },
    };
    let mut cs = TestConstraintSystem::<Bn256>::new();

    circuit.synthesize(&mut cs).expect("synthesis failed");
    if !cs.is_satisfied() {
      println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
    }

    TestResult::from_bool(cs.is_satisfied())
  }
}
