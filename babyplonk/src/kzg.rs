use ark_ff::Field;
use ark_poly::{
    DenseUVPolynomial, Polynomial,
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
};

use crate::pairing::pairing;
use crate::tiny_field::{G1Point, G2Point, ScalarField};

pub trait PolyCommit: Clone {
    type Field;
    type Polynomial;
    type Commitment;
    type Proof;

    fn setup(max_degree: usize, tau: Self::Field) -> Self;
    fn commit(&self, poly: &Self::Polynomial) -> Self::Commitment;
    fn open(&self, poly: &Self::Polynomial, point: Self::Field) -> (Self::Field, Self::Proof);
    fn verify(
        &self,
        commitment: &Self::Commitment,
        point: Self::Field,
        value: Self::Field,
        proof: &Self::Proof,
    ) -> bool;
}

#[derive(Debug, Clone)]
pub struct SRS {
    pub g1_powers: Vec<G1Point>,
    pub g2: G2Point,
    pub g2_tau: G2Point,
}

#[derive(Debug, Clone)]
pub struct KZG10 {
    pub srs: SRS,
}

impl PolyCommit for KZG10 {
    type Field = ScalarField;
    type Polynomial = DensePolynomial<ScalarField>;
    type Commitment = G1Point;
    type Proof = G1Point;

    fn setup(max_degree: usize, tau: ScalarField) -> Self {
        let g1 = G1Point::generator();
        let g2 = G2Point::generator();

        let mut g1_powers = Vec::with_capacity(max_degree + 1);
        let mut tau_power = ScalarField::ONE;
        for _ in 0..=max_degree {
            g1_powers.push(g1.scalar_mul_fr(tau_power));
            tau_power *= tau;
        }

        let g2_tau = g2.scalar_mul_fr(tau);
        let srs = SRS {
            g1_powers,
            g2,
            g2_tau,
        };
        KZG10 { srs }
    }

    fn commit(&self, poly: &Self::Polynomial) -> Self::Commitment {
        if poly.coeffs.is_empty() {
            return G1Point::Infinity;
        }
        if poly.coeffs.len() > self.srs.g1_powers.len() {
            panic!("polynomial degree exceeds SRS size");
        }

        let mut acc = G1Point::Infinity;
        for (i, coeff) in poly.coeffs.iter().enumerate() {
            if *coeff == ScalarField::ZERO {
                continue;
            }
            let term = self.srs.g1_powers[i].scalar_mul_fr(*coeff);
            acc = acc.add(&term);
        }
        acc
    }

    fn open(&self, poly: &Self::Polynomial, point: Self::Field) -> (Self::Field, Self::Proof) {
        let value = poly.evaluate(&point);
        let divisor = DensePolynomial::from_coefficients_vec(vec![-point, ScalarField::ONE]);
        let poly_ds = DenseOrSparsePolynomial::from(poly);
        let divisor_ds = DenseOrSparsePolynomial::from(&divisor);
        let (quotient, remainder) = poly_ds
            .divide_with_q_and_r(&divisor_ds)
            .expect("division by non-zero polynomial must succeed");
        debug_assert_eq!(
            remainder
                .coeffs
                .first()
                .cloned()
                .unwrap_or(ScalarField::ZERO),
            value
        );
        let proof = self.commit(&quotient);
        (value, proof)
    }

    fn verify(
        &self,
        commitment: &Self::Commitment,
        point: Self::Field,
        value: Self::Field,
        proof: &Self::Proof,
    ) -> bool {
        let g1 = G1Point::generator();
        let g1_value = g1.scalar_mul_fr(value);
        let left_g1 = commitment.sub(&g1_value);

        let g2_point = self.srs.g2.scalar_mul_fr(point);
        let right_g2 = self.srs.g2_tau.sub(&g2_point);

        let left = pairing(&left_g1, &self.srs.g2);
        let right = pairing(proof, &right_g2);
        left == right
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kzg10_open_and_verify_success() {
        let tau = ScalarField::from(5u64);
        let kzg = KZG10::setup(8, tau);
        let poly = DensePolynomial::from_coefficients_vec(vec![
            ScalarField::from(3u64),
            ScalarField::from(7u64),
            ScalarField::from(2u64),
        ]);
        let point = ScalarField::from(11u64);

        let commitment = kzg.commit(&poly);
        let (value, proof) = kzg.open(&poly, point);
        assert!(kzg.verify(&commitment, point, value, &proof));
    }

    #[test]
    fn test_kzg10_open_and_verify_failure() {
        let tau = ScalarField::from(5u64);
        let kzg = KZG10::setup(8, tau);
        let poly = DensePolynomial::from_coefficients_vec(vec![
            ScalarField::from(3u64),
            ScalarField::from(7u64),
            ScalarField::from(2u64),
        ]);
        let point = ScalarField::from(11u64);

        let commitment = kzg.commit(&poly);
        let (value, proof) = kzg.open(&poly, point);
        let wrong_value = value + ScalarField::from(10u64);

        assert!(!kzg.verify(&commitment, point, wrong_value, &proof));
    }
}
