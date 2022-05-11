use sapling_crypto::bellman::pairing::ff::{Field, PrimeField};
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
use sapling_crypto::circuit::num::AllocatedNum;
use OptionExt;

pub const LOG_TREE_SIZE: usize = 10;

pub fn double_mimc<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, mut xl: AllocatedNum<E>, mut xr: AllocatedNum<E>) -> Result<AllocatedNum<E>, SynthesisError>
where
  E::Fr: PrimeField,
{
  let mimc_params = vec![E::Fr::from_str("1").unwrap(), E::Fr::from_str("2").unwrap()];

  for (i, c) in mimc_params.iter().cloned().enumerate() {
    // xL, xR := xR + (xL + Ci)^3, xL
    let cs = &mut cs.namespace(|| format!("round {}", i));

    // tmp = (xL + Ci)^2
    let tmp = AllocatedNum::alloc(cs.namespace(|| "x2 result"), || {
      let mut t = xl.get_value().grab()?.clone();
      t.add_assign(&c);
      t.square();
      Ok(t)
    })?;

    cs.enforce(|| "tmp = (xL + Ci)^2", |lc| lc + xl.get_variable() + (c.into(), CS::one()), |lc| lc + xl.get_variable() + (c.into(), CS::one()), |lc| lc + tmp.get_variable());

    // new_xL = xR + (xL + Ci)^3
    // new_xL = xR + tmp * (xL + Ci)
    // new_xL - xR = tmp * (xL + Ci)
    let new_xl = AllocatedNum::alloc(&mut *cs, || {
      let mut t = xl.get_value().grab()?.clone();
      t.add_assign(&c);
      t.mul_assign(&tmp.get_value().unwrap());
      t.add_assign(&xr.get_value().unwrap());
      Ok(t)
    })?;

    cs.enforce(|| "new_xL = xR + (xL + Ci)^3", |lc| lc + tmp.get_variable(), |lc| lc + xl.get_variable() + (c.into(), CS::one()), |lc| lc + new_xl.get_variable() - xr.get_variable());

    // xR = xL
    xr = xl;

    // xL = new_xL
    xl = new_xl;
  }

  Ok(xl)
}

pub fn mimc<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS, data: &[AllocatedNum<E>]) -> Result<AllocatedNum<E>, SynthesisError> {
  assert!(data.len() >= 2);
  let mut accum = double_mimc(cs, data[0].clone(), data[1].clone())?;
  for w in data[2..].iter() {
    accum = double_mimc(cs, accum, w.clone())?;
  }
  Ok(accum)
}

pub mod helper {
  use super::*;

  pub fn double_mimc<F: PrimeField>(mut xl: F, mut xr: F) -> F {
    let mimc_params = vec![F::from_str("1").unwrap(), F::from_str("2").unwrap()];

    for c in mimc_params.iter() {
      let mut tmp1 = xl;
      tmp1.add_assign(c);

      let mut tmp2 = tmp1;
      tmp2.square();

      tmp2.mul_assign(&tmp1);
      tmp2.add_assign(&xr);
      xr = xl;
      xl = tmp2;
    }

    xl
  }

  pub fn mimc<F: PrimeField>(data: &[F]) -> F {
    assert!(data.len() >= 2);
    let mut accum = double_mimc(data[0], data[1]);
    for w in data[2..].iter() {
      accum = double_mimc(accum, *w);
    }
    accum
  }
}
