use hs_bindgen::*;
use ark_ec::{Group, VariableBaseMSM};
use ark_ff::{PrimeField, Field};
// We'll use the BLS12-381 G1 curve for this example.
// This group has a prime order `r`, and is associated with a prime field `Fr`.
// use ark_bls12_381::{G1Projective as G, G1Affine as GAffine, Fr as ScalarField};
use ark_test_curves::bls12_381::{G1Projective as G, G1Affine as GAffine, Fr as ScalarField};
use ark_std::{Zero,  UniformRand};

#[hs_bindgen]
fn hello(name: &str) {
    println!("Hello, {name}!");
}

impl FromReprRust for GAffine {
        fn from(ptr: *const i8) -> Self {
            GAffine {
                name: <String as FromReprRust<*const i8>>::from(ptr),
                kind: PhantomData::<T>
            }
        }    
}

#[hs_bindgen]
pub fn add(left: GAffine, right: GAffine) -> GAffine {
    left + right
}

// #[hs_bindgen(add :: CUInt -> CUInt -> CUInt)]
// pub fn add(left: u32, right: u32) -> u32 {
//     let result = (left + right).into();
//     println!("Result: {}!", result);
//     result
// }

// #[hs_bindgen]
pub fn scalar_mult(a: GAffine, b: GAffine, s1: ScalarField, s2: ScalarField) -> GAffine {
    G::msm(&[a, b], &[s1, s2]).unwrap().into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }

    #[test]
    fn it_arkworks() {
        let mut rng = ark_std::test_rng();
        // Let's sample uniformly random group elements:
        let a = GAffine::rand(&mut rng);
        let b = GAffine::rand(&mut rng);
        
        let s1 = ScalarField::rand(&mut rng);
        let s2 = ScalarField::rand(&mut rng);
        
        // Note that we're using the `GAffine` type here, as opposed to `G`.
        // This is because MSMs are more efficient when the group elements are in affine form. (See below for why.)
        //
        // The `VariableBaseMSM` trait allows specializing the input group element representation to allow
        // for more efficient implementations.
        let r = scalar_mult(a, b, s1, s2);
        assert_eq!(r, a * s1 + b * s2);        
    }
}
