// use hs_bindgen::*;
// use hs_bindgen_attribute::*;
// use hs_bindgen_traits::*;
use std::{
 io::Write,
 marker::PhantomData,
 ops::Deref,
 sync::atomic::{AtomicUsize, Ordering},
};

use haskell_ffi::{
 error::Result,
 from_haskell::{marshall_from_haskell_fixed, marshall_from_haskell_var},
 haskell_max_size::HaskellMaxSize,
 to_haskell::{
     marshall_result_to_haskell_var, marshall_to_haskell_external, marshall_to_haskell_fixed,
     marshall_to_haskell_max, marshall_to_haskell_var,
 },
 FromHaskell, HaskellSize, ToHaskell,
};

use borsh::{BorshDeserialize, BorshSerialize};

use der::Encode;

use ark_ff::{BigInteger, PrimeField};
use ark_ff::biginteger::BigInt;
use ark_ec::{VariableBaseMSM};
use ark_ec::AffineRepr;
// use ark_ff::{PrimeField, Field};
// We'll use the BLS12-381 G1 curve for this example.
// This group has a prime order `r`, and is associated with a prime field `Fr`.
// use ark_bls12_381::{G1Projective as G, G1Affine as GAffine, Fr as ScalarField};
use ark_test_curves::bls12_381::{G1Projective as G, G1Affine as GAffine, Fr as ScalarField};
// use ark_std::UniformRand;
// use ark_std::marker::PhantomData;
// use crate::traits::FromReprRust;

// #[hs_bindgen]
// fn hello(name: &str) {
//     println!("Hello, {name}!");
// }

// type GAffine = <G as CurveGroup>::Affingp

// impl FromReprRust<*const i8> for G1Affine {
    // fn from(ptr: *const i8) -> Self {
        // GAffine {
            // name: <String as FromReprRust<*const i8>>::from(ptr),
            // kind: PhantomData::<T>
        // }
    // }
// }

// #[hs_bindgen]
// pub fn add(left: GAffine, right: GAffine) -> GAffine {
    // left + right
// }

// #[hs_bindgen(add :: CUInt -> CUInt -> CUInt)]
// pub fn add(left: u32, right: u32) -> u32 {
//     // let result = (left + right).into();
//     let result = left + right;
//     println!("Result: {}!", result);
//     result
// }

pub enum RW {}

/// cbindgen:ignore
pub const RW: PhantomData<RW> = PhantomData;

impl FromHaskell<RW> for GAffine {
  fn from_haskell(buf: &mut &[u8], tag: PhantomData<RW>) -> Result<Self> {
      let (x, y) = <([u64; 6], [u64; 6])>::from_haskell(buf, tag)?;
      Ok(GAffine::new(BigInt::new(x).into(), BigInt::new(y).into()))
    }
}

impl ToHaskell<RW> for GAffine {
    fn to_haskell<W: Write>(&self, writer: &mut W, tag: PhantomData<RW>) -> Result<()> {
        let x = self.x().unwrap().into_bigint().0;
        let y = self.y().unwrap().into_bigint().0;
        (x, y).to_haskell(writer, tag)?;
        Ok(())
    }
}

#[no_mangle]
pub fn scalar_mult(a: GAffine, b: GAffine, s1: ScalarField, s2: ScalarField) -> GAffine {
    G::msm(&[a, b], &[s1, s2]).unwrap().into()
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn it_works() {
//         let result = add(2, 2);
//         assert_eq!(result, 4);
//     }

//     #[test]
//     fn it_arkworks() {
//         let mut rng = ark_std::test_rng();
//         // Let's sample uniformly random group elements:
//         let a = GAffine::rand(&mut rng);
//         let b = GAffine::rand(&mut rng);
//         println!("Result: {}!", a.x);

//         let s1 = ScalarField::rand(&mut rng);
//         let s2 = ScalarField::rand(&mut rng);

//         // Note that we're using the `GAffine` type here, as opposed to `G`.
//         // This is because MSMs are more efficient when the group elements are in affine form. (See below for why.)
//         //
//         // The `VariableBaseMSM` trait allows specializing the input group element representation to allow
//         // for more efficient implementations.
//         let r = scalar_mult(a, b, s1, s2);
//         assert_eq!(r, a * s1 + b * s2);
//     }
// }
