extern crate vdf_zkp;
use num_traits::Pow;
use vdf_zkp::group::{SemiGroup, RsaGroup};

extern crate num_bigint;
extern crate rand;
extern crate num_traits;
use num_bigint::{BigUint, RandBigInt};
use std::convert::TryInto;
use num_traits::cast::FromPrimitive;

use rand::Rng;
use std::ptr::hash;
use std::str::FromStr;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;

const RSA_2048: &str = "25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357";

/*
pub struct SetupParam <'a, G:SemiGroup> { 
   g: &'a G::Elem,
   g_t : &'a G::Elem,   
   g_t_one: &'a G::Elem,
}
*/
#[derive(Debug)]
pub struct SetupParam {
   g : BigUint,
   g_t_plus_one : BigUint,
   g_t : BigUint,
   //
   n : BigUint,
   b : BigUint,
}

#[derive(Debug)]
pub struct Sigma_Proof {
   r_1 : BigUint,
   r_3 : BigUint,
   s_1 : BigUint,
   s_3 : BigUint,
   k : u128,
   
   c : u64,    //temp
}

// Setup

//fn Setup<'a, G: SemiGroup>(b: BigUint, N: BigUint, t : BigUint ) -> SetupParam { 
fn Setup(b: BigUint, N: BigUint, t : BigUint ) -> SetupParam { 
    
   let g = RsaGroup { n: N.clone(), g: BigUint::from(2usize)};

   SetupParam {
      g: g.power(&b, &BigUint::from(1usize)),
      g_t: g.power(&b,&t),
      g_t_plus_one: g.power(&b, &(t+1usize)),
      n : N.clone(),
      b : BigUint::from(2usize),
   }
}

// Prove
fn Prove(param: &SetupParam) -> Sigma_Proof {

   let rsa_g = RsaGroup { n: param.n.clone(), g: param.b.clone() };
   let base = param.b.clone();
   let g = param.g.clone();
   let g_t = param.g_t.clone();
   let g_t_plus_one = param.g_t_plus_one.clone();

   // 1. choose random s,r from F
   let mut rng = rand::thread_rng();
   let s = rng.gen::<u64>();
   let r = rng.gen::<u64>();
   println!("1.choose random s, r :{} ,{}", s,r);

   // 2. R_1 <- g^r ; R_3 <- (g^(2^(T+1)))^r
   let r_1 = rsa_g.power(&g, &BigUint::from_u64(r).unwrap());
   let r_3 = rsa_g.power( &g_t_plus_one, &BigUint::from_u64(r).unwrap());
   println!("2. R_1, R_3 : {} , {}", r_1, r_3);

   // 3. c <- H(R_1, R_3) ; k <- r + c * s
   let mut hasher = DefaultHasher::new();
   hasher.write_u64(s);
   hasher.write_u64(r);
   let c = hasher.finish();
   let k :u128 = (r as u128 + (c as u128 * s as u128)).into();
   println!("3. c, k : {}, {}", c, k);

   // 4. S_1 <- g^s ; S_2 <- (g^(2^T))^s ; S_3 <- (g^(2^(T+1)))^s
   // ** S_1 is an encryption key
   let s_1 = rsa_g.power(&g, &BigUint::from_u64(s).unwrap());
   let s_2 = rsa_g.power(&g_t, &BigUint::from_u64(s).unwrap());
   let s_3 = rsa_g.power(&g_t_plus_one, &BigUint::from_u64(s).unwrap());
   println!("4. s_1, s_2, s_3 : {} , {} , {}", s_1, s_2, s_3);

   // sigma_proof <- (R_1, R_2, S_1, S_3, k)
   Sigma_Proof { 
      r_1: r_1.clone(), 
      r_3: r_3.clone(), 
      s_1: s_1.clone(),
      s_3: s_3.clone(), 
      k: k,

      c: c,
   }
}

// Verify
fn Verify(param: &SetupParam ,proof: &Sigma_Proof) -> bool {

   // 0. parse proof -> R_1, R_3, S_1, S_3, k
   let rsa_g = RsaGroup { n: param.n.clone(), g: param.b.clone() };
   let r_1 = proof.r_1.clone();
   let r_3 = proof.r_3.clone();
   let s_1 = proof.s_1.clone();
   let s_3 = proof.s_3.clone();

   // 1. c <- H(R_1, R_3)
   let c = proof.c;
   /*
   let mut hasher = DefaultHasher::new();
   hasher.write_u64(i)
   */

   // 2. g_k <- R_1 * S_1^c ; (g_(2^(T+1)))^k = R_3 * S_3^c
   let c_bu = BigUint::from_u64(c).unwrap();
   //let s_1_c = s_1.pow(c_bu.clone());
   let s_1_c = rsa_g.power(&s_1, &c_bu);
   let temp_1 = s_1_c * r_1;
   let g_k_out = rsa_g.power(&temp_1, &BigUint::from_usize(1usize).unwrap());
   //let g_k = param.g.clone().pow(BigUint::from_u128(proof.k).unwrap());
   let g_k = rsa_g.power(&param.g, &BigUint::from_u128(proof.k).unwrap());
   println!("g_k : {}", g_k);
   println!("g_k_out : {}", g_k_out);

   //let s_3_c = s_3.pow(c_bu.clone());
   let s_3_c = rsa_g.power(&s_3, &c_bu);
   let temp_3 = s_3_c * r_3 ;
   let g_t_plus_one_k_out = rsa_g.power(&temp_3, &BigUint::from_usize(1usize).unwrap());
   //let g_one_k = param.g_t_plus_one.clone().pow(BigUint::from_u128(proof.k).unwrap());
   let g_one_k = rsa_g.power(&param.g_t_plus_one, &BigUint::from_u128(proof.k).unwrap());
   println!("g_k : {}", g_one_k);
   println!("g_t_plus_one :{}", g_t_plus_one_k_out);

   (g_one_k == g_t_plus_one_k_out) && (g_k == g_k_out)
}



#[test]
fn o_sigma_work() {

   // 0. Setup 
   //    pp = (g, g^(2^T), g^(2^(T+1)))
   let base = BigUint::from(2usize);
   let n = BigUint::from_str(RSA_2048).unwrap();
   //let t = BigUint::from(2usize);
   let t :u32 = 2;
   let pow_t = BigUint::from(2usize).pow(t);

   let param = Setup(base, n, pow_t);
   println!("Setup Parameter : {:?}", param);

   let proof = Prove(&param);
   println!("Proof : {:?}", proof);

   let verify = Verify(&param, &proof);
   println!("Verify: {}", verify);

}