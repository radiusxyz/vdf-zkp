### Test

> cargo test --package vdf_zkp --lib -- vdf::tests --nocapture

### Use a lib

1. Import the library in `Cargo.toml`

```md
fastrand = "1.7.0"
sapling-crypto = { package = "sapling-crypto_ce", git = "https://github.com/matter-labs-archive/sapling-crypto" }
vdf_zkp = { package = "vdf_zkp", git = "https://github.com/radiusxyz/vdf-zkp" }
```

2. Use the library

```rust
use sapling_crypto::bellman::pairing::bls12_381::Bls12;
use vdf_zkp::{nat_to_f, init_big_uint_from_str, VdfZKP};

let mut vdf_zkp = VdfZKP::<Bls12>::new();
vdf_zkp.setup_parameter(); // or vdf_zkp.import_parameter();

let vdf_params = vdf_zkp.clone().vdf_params.unwrap(); // Get vdf parameters

vdf_zkp.export_parameter(); // Option

// Generate random (128 bits)
let s: u128 = fastrand::u128(..);
let s = BigUint::from(s);

init_big_uint_from_str!(g_two_t, vdf_params.g_two_t.as_str());
init_big_uint_from_str!(n, vdf_params.n.as_str());

let s2 = g_two_t.modpow(&s, &n); // s2 == y / It is used at encryption as a symmetric key
let s2_field = nat_to_f::<<Bls12 as ScalarEngine>::Fr>(&s2).unwrap();

// Generate commitment of s2
let commitment = mimc::helper::mimc(&[s2_field.clone(), s2_field.clone()]);

// Generate proof
let proof = vdf_zkp.generate_proof(commitment, s.to_string().as_str());

// Verify proof
let is_varified = vdf_zkp.verify(commitment, proof); // true or false
```

- **commitment**:
  - It is a commitment between VDF and Encryption proof.
  - It means that they have the same symmetric key(== y | == s2).
