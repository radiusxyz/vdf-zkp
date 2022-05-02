use bignat::BigNat;
use gadget::Gadget;
use group::{CircuitSemiGroup, SemiGroup};
use num_bigint::BigUint;
use sapling_crypto::bellman::pairing::Engine;
use sapling_crypto::bellman::{ConstraintSystem, LinearCombination, SynthesisError};
use std::collections::BTreeSet;
use std::fmt::Debug;
use wesolowski::proof_of_exp;

pub trait IntSet: Sized + Clone + Eq + Debug {
  type G: SemiGroup;

  fn new(group: Self::G) -> Self;

  fn new_with<I: IntoIterator<Item = BigUint>>(group: Self::G, items: I) -> Self;

  /// Add `n` to the set, returning whether `n` is new to the set.
  fn insert(&mut self, n: BigUint) -> bool;
  /// Remove `n` from the set, returning whether `n` was present.
  fn remove(&mut self, n: &BigUint) -> bool;
  /// BigUinthe digest of the current elements (`g` to the product of the elements).
  fn digest(&self) -> <Self::G as SemiGroup>::Elem;

  /// Gets the underlying RSA group
  fn group(&self) -> &Self::G;

  /// Add all of the `ns` to the set. Returns whether all items were absent
  fn insert_all<I: IntoIterator<Item = BigUint>>(&mut self, ns: I) -> bool {
    let mut all_absent = true;
    for n in ns {
      all_absent &= self.insert(n);
    }
    all_absent
  }

  /// Remove all of the `ns` from the set. Rerturns whether all items were present.
  fn remove_all<'a, I: IntoIterator<Item = &'a BigUint>>(&mut self, ns: I) -> bool
  where
    <Self::G as SemiGroup>::Elem: 'a,
  {
    let mut all_present = true;
    for n in ns {
      all_present &= self.remove(n);
    }
    all_present
  }
}

/// An `NaiveExpSet` which computes products from scratch each time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NaiveExpSet<G: SemiGroup> {
  group: G,
  elements: BTreeSet<BigUint>,
}

impl<G: SemiGroup> IntSet for NaiveExpSet<G>
where
  G::Elem: Ord,
{
  type G = G;

  fn new(group: G) -> Self {
    Self { group, elements: BTreeSet::new() }
  }

  fn new_with<I: IntoIterator<Item = BigUint>>(group: G, items: I) -> Self {
    let mut this = Self::new(group);
    this.insert_all(items);
    this
  }

  fn insert(&mut self, n: BigUint) -> bool {
    self.elements.insert(n)
  }

  fn remove(&mut self, n: &BigUint) -> bool {
    self.elements.remove(n)
  }

  fn digest(&self) -> G::Elem {
    self.elements.iter().fold(self.group.generator(), |acc, elem| self.group.power(&acc, &elem))
  }

  fn group(&self) -> &G {
    &self.group
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CircuitIntSet<E, CG, S>
where
  E: Engine,
  CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
  CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
  S: IntSet<G = CG::Group>,
{
  pub value: Option<S>,
  pub group: CG,
  pub digest: CG::Elem,
}

impl<E, CG, S> Gadget for CircuitIntSet<E, CG, S>
where
  E: Engine,
  CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
  CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
  S: IntSet<G = CG::Group>,
{
  type E = E;
  type Value = S;
  type Params = ();
  type Access = CG;
  fn alloc<CS: ConstraintSystem<E>>(
    mut cs: CS,
    value: Option<&Self::Value>, //
    access: CG,                  // group
    _params: &(),
  ) -> Result<Self, SynthesisError> {
    let digest_val = value.map(|v| v.digest());
    let digest: CG::Elem = <CG::Elem as Gadget>::alloc(cs.namespace(|| "digest"), digest_val.as_ref(), (), &CG::elem_params(access.params()))?;
    let group = access;
    Ok(Self { value: value.cloned(), digest, group })
  }
  fn wires(&self) -> Vec<LinearCombination<E>> {
    self.digest.wires()
  }
  fn wire_values(&self) -> Option<Vec<E::Fr>> {
    self.digest.wire_values()
  }
  fn value(&self) -> Option<&Self::Value> {
    self.value.as_ref()
  }
  fn params(&self) -> &Self::Params {
    &()
  }
  fn access(&self) -> &Self::Access {
    &self.group
  }
}

impl<E, CG, S> CircuitIntSet<E, CG, S>
where
  E: Engine,
  CG: CircuitSemiGroup<E = E> + Gadget<E = E, Value = <CG as CircuitSemiGroup>::Group>,
  CG::Elem: Gadget<E = E, Value = <CG::Group as SemiGroup>::Elem, Access = ()>,
  S: IntSet<G = CG::Group>,
{
  pub fn remove<CS: ConstraintSystem<E>>(self, mut cs: CS, challenge: &BigNat<E>, items: &[BigNat<E>]) -> Result<Self, SynthesisError> {
    let value = self.value.clone().and_then(|mut set| {
      items.iter().map(|i| i.value.as_ref()).collect::<Option<Vec<&BigUint>>>().map(|is| {
        assert!(set.remove_all(is));
        set
      })
    });
    let new_set = Self::alloc(cs.namespace(|| "new"), value.as_ref(), self.group.clone(), &())?;
    proof_of_exp(cs.namespace(|| "proof"), &new_set.group, &new_set.digest, items, challenge, &self.digest)?;
    Ok(new_set)
  }

  pub fn insert<CS: ConstraintSystem<E>>(self, mut cs: CS, challenge: &BigNat<E>, items: &[BigNat<E>]) -> Result<Self, SynthesisError> {
    let value = self.value.clone().and_then(|mut set| {
      items.iter().map(|i| i.value.clone()).collect::<Option<Vec<BigUint>>>().map(|is| {
        assert!(set.insert_all(is));
        set
      })
    });
    let new_set = Self::alloc(cs.namespace(|| "new"), value.as_ref(), self.group.clone(), &())?;
    proof_of_exp(cs.namespace(|| "proof"), &new_set.group, &self.digest, items, challenge, &new_set.digest)?;
    Ok(new_set)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use test_helpers::*;

  use group::{CircuitRsaGroup, CircuitRsaGroupParams, RsaGroup};
  use OptionExt;

  use std::str::FromStr;

  pub struct RsaRemovalInputs<'a> {
    pub g: &'a str,
    pub m: &'a str,
    pub initial_items: &'a [&'a str],
    pub removed_items: &'a [&'a str],
    pub initial_digest: &'a str,
    pub challenge: &'a str,
    pub final_digest: &'a str,
  }

  pub struct RsaRemovalParams {
    pub limb_width: usize,
    pub n_limbs_b: usize,
    pub n_limbs_e: usize,
  }

  pub struct RsaRemoval<'a> {
    inputs: Option<RsaRemovalInputs<'a>>,
    params: RsaRemovalParams,
  }

  impl<'a, E: Engine> Circuit<E> for RsaRemoval<'a> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
      let challenge = BigNat::alloc_from_nat(cs.namespace(|| "challenge"), || Ok(BigUint::from_str(self.inputs.grab()?.challenge).unwrap()), self.params.limb_width, self.params.n_limbs_b)?;
      let initial_items_vec: Vec<BigUint> = self.inputs.grab()?.initial_items.iter().map(|i| BigUint::from_str(i).unwrap()).collect();
      let removed_items_vec: Vec<BigNat<E>> = self
        .inputs
        .grab()?
        .removed_items
        .iter()
        .enumerate()
        .map(|(i, e)| BigNat::alloc_from_nat(cs.namespace(|| format!("removed item {}", i)), || Ok(BigUint::from_str(e).unwrap()), self.params.limb_width, self.params.n_limbs_e))
        .collect::<Result<Vec<BigNat<E>>, SynthesisError>>()?;
      let initial_digest = BigNat::alloc_from_nat(cs.namespace(|| "initial_digest"), || Ok(BigUint::from_str(self.inputs.grab()?.initial_digest).unwrap()), self.params.limb_width, self.params.n_limbs_b)?;

      let final_digest = BigNat::alloc_from_nat(cs.namespace(|| "final_digest"), || Ok(BigUint::from_str(self.inputs.grab()?.final_digest).unwrap()), self.params.limb_width, self.params.n_limbs_b)?;
      let raw_group = RsaGroup {
        g: BigUint::from_str(self.inputs.grab()?.g).unwrap(),
        n: BigUint::from_str(self.inputs.grab()?.m).unwrap(),
      };

      let group = CircuitRsaGroup::alloc(
        cs.namespace(|| "group"),
        Some(&raw_group),
        (),
        &CircuitRsaGroupParams {
          g_word_width: self.params.limb_width,
          g_word_count: self.params.n_limbs_b,
          n_word_width: self.params.limb_width,
          n_word_count: self.params.n_limbs_b,
        },
      )?;

      println!("Set group");
      println!("g : {:?}", &group.g.to_string());
      println!("n : {:?}", &group.n.to_string());

      let initial_set: CircuitIntSet<E, CircuitRsaGroup<E>, NaiveExpSet<RsaGroup>> = CircuitIntSet::alloc(cs.namespace(|| "initial_set"), Some(&NaiveExpSet::new_with(raw_group, initial_items_vec.into_iter())), group.clone(), &())?;

      initial_set.digest.equal(cs.namespace(|| "initial_eq"), &initial_digest)?;

      let final_set = initial_set.remove(cs.namespace(|| "removal"), &challenge, &removed_items_vec)?;

      final_set.digest.equal(cs.namespace(|| "final_eq"), &final_digest)?;
      Ok(())
    }
  }

  circuit_tests! {
      removal_init_empty: (
                              RsaRemoval {
                                  inputs: Some(RsaRemovalInputs {
                                      g: "2",
                                      m: "143",
                                      initial_items: &[
                                      ],
                                      removed_items: &[
                                      ],
                                      challenge: "223",
                                      initial_digest: "2",
                                      final_digest: "2",
                                  }),
                                  params: RsaRemovalParams {
                                      limb_width: 4,
                                      n_limbs_e: 2,
                                      n_limbs_b: 2,
                                  }
                              } ,
                              true
                          ),
                          removal_init_3_remove_3: (
                              RsaRemoval {
                                  inputs: Some(RsaRemovalInputs {
                                      g: "2",
                                      m: "143",
                                      initial_items: &[
                                          "3",
                                      ],
                                      removed_items: &[
                                          "3",
                                      ],
                                      challenge: "223",
                                      initial_digest: "8",
                                      final_digest: "2",
                                  }),
                                  params: RsaRemovalParams {
                                      limb_width: 4,
                                      n_limbs_e: 2,
                                      n_limbs_b: 2,
                                  }
                              } ,
                              true
                                  ),
                                  removal_init_3_remove_3_wrong: (
                                      RsaRemoval {
                                          inputs: Some(RsaRemovalInputs {
                                              g: "2",
                                              m: "143",
                                              initial_items: &[
                                                  "3",
                                              ],
                                              removed_items: &[
                                                  "3",
                                              ],
                                              challenge: "223",
                                              initial_digest: "8",
                                              final_digest: "3",
                                          }),
                                          params: RsaRemovalParams {
                                              limb_width: 4,
                                              n_limbs_e: 2,
                                              n_limbs_b: 2,
                                          }
                                      } ,
                                      false
                                          ),
                                          removal_init_3_5_7_remove_3: (
                                              RsaRemoval {
                                                  inputs: Some(RsaRemovalInputs {
                                                      g: "2",
                                                      m: "143",
                                                      initial_items: &[
                                                          "3",
                                                          "5",
                                                          "7",
                                                      ],
                                                      removed_items: &[
                                                          "3",
                                                      ],
                                                      challenge: "223",
                                                      initial_digest: "109",
                                                      final_digest: "98",
                                                  }),
                                                  params: RsaRemovalParams {
                                                      limb_width: 4,
                                                      n_limbs_e: 2,
                                                      n_limbs_b: 2,
                                                  }
                                              } ,
                                              true
                                                  ),
                                                  removal_init_3_5_7_remove_3_5: (
                                                      RsaRemoval {
                                                          inputs: Some(RsaRemovalInputs {
                                                              g: "2",
                                                              m: "143",
                                                              initial_items: &[
                                                                  "3",
                                                                  "5",
                                                                  "7",
                                                              ],
                                                              removed_items: &[
                                                                  "3",
                                                                  "5",
                                                              ],
                                                              challenge: "223",
                                                              initial_digest: "109",
                                                              final_digest: "128",
                                                          }),
                                                          params: RsaRemovalParams {
                                                              limb_width: 4,
                                                              n_limbs_e: 2,
                                                              n_limbs_b: 2,
                                                          }
                                                      } ,
                                                      true
                                                          ),
  }
}
