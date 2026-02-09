use ark_ff::{Field, Zero};
use ark_poly::{
    DenseUVPolynomial, Polynomial,
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
};

use crate::kzg::{KZG10, PolyCommit};
use crate::tiny_field::{G1Point, ScalarField};

pub fn linear_domain(n: usize, step: usize) -> Vec<ScalarField> {
    assert!(step > 0, "step must be non-zero");
    (1..=n)
        .step_by(step)
        .map(|i| ScalarField::from(i as u64))
        .collect()
}

fn vanishing_poly(domain: &[ScalarField]) -> DensePolynomial<ScalarField> {
    let mut poly = DensePolynomial::from_coefficients_vec(vec![ScalarField::ONE]);
    for &x in domain {
        let factor = DensePolynomial::from_coefficients_vec(vec![-x, ScalarField::ONE]);
        poly = &poly * &factor;
    }
    poly
}

fn interpolate(domain: &[ScalarField], values: &[ScalarField]) -> DensePolynomial<ScalarField> {
    assert_eq!(domain.len(), values.len());
    let n = domain.len();
    let mut acc = DensePolynomial::zero();
    for i in 0..n {
        let mut num = DensePolynomial::from_coefficients_vec(vec![ScalarField::ONE]);
        let mut den = ScalarField::ONE;
        for j in 0..n {
            if i == j {
                continue;
            }
            let factor = DensePolynomial::from_coefficients_vec(vec![-domain[j], ScalarField::ONE]);
            num = &num * &factor;
            den *= domain[i] - domain[j];
        }
        let scale = values[i] * den.inverse().unwrap();
        acc = &acc + &(&num * scale);
    }
    acc
}

pub struct ZeroTestProof {
    pub f_commit: G1Point,
    pub q_commit: G1Point,
    pub r: ScalarField,
    pub f_eval: ScalarField,
    pub q_eval: ScalarField,
    pub f_proof: G1Point,
    pub q_proof: G1Point,
}

pub struct ZeroTest;

impl ZeroTest {
    // Prove that f(x) = 0 for all x in domain.
    pub fn prove(
        kzg: &KZG10,
        f: &DensePolynomial<ScalarField>,
        domain: &[ScalarField],
        r: ScalarField,
    ) -> ZeroTestProof {
        let z = vanishing_poly(domain);
        let (q, rem) = DenseOrSparsePolynomial::from(f)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&z))
            .expect("division by non-zero polynomial must succeed");
        debug_assert!(rem.is_zero());

        let f_commit = kzg.commit(f);
        let q_commit = kzg.commit(&q);

        let (f_eval, f_proof) = kzg.open(f, r);
        let (q_eval, q_proof) = kzg.open(&q, r);

        ZeroTestProof {
            f_commit,
            q_commit,
            r,
            f_eval,
            q_eval,
            f_proof,
            q_proof,
        }
    }

    pub fn verify(kzg: &KZG10, domain: &[ScalarField], proof: &ZeroTestProof) -> bool {
        let z = vanishing_poly(domain);
        let z_r = z.evaluate(&proof.r);
        if !kzg.verify(&proof.f_commit, proof.r, proof.f_eval, &proof.f_proof) {
            return false;
        }
        if !kzg.verify(&proof.q_commit, proof.r, proof.q_eval, &proof.q_proof) {
            return false;
        }
        proof.f_eval == proof.q_eval * z_r
    }
}

pub struct ProductCheckProof {
    pub f_commit: G1Point,
    pub t_commit: G1Point,
    pub h_proof: ZeroTestProof,
    pub first_eval: ScalarField,
    pub first_proof: G1Point,
    pub first_point: ScalarField,
}

pub struct ProductCheck;

impl ProductCheck {
    // Product check on domain: prove that ∏_{x in domain} f(x) = 1.
    pub fn prove(
        kzg: &KZG10,
        f: &DensePolynomial<ScalarField>,
        domain: &[ScalarField],
        r: ScalarField,
    ) -> ProductCheckProof {
        let n = domain.len();
        let mut f_vals = Vec::with_capacity(n);
        for &x in domain {
            f_vals.push(f.evaluate(&x));
        }

        let mut t_vals = vec![ScalarField::ZERO; n];
        if n > 0 {
            t_vals[0] = ScalarField::ONE;
            for i in 1..n {
                t_vals[i] = t_vals[i - 1] * f_vals[i];
            }
        }

        let t = interpolate(domain, &t_vals);

        let mut f_shift_vals = vec![ScalarField::ZERO; n];
        let mut t_shift_vals = vec![ScalarField::ZERO; n];
        for i in 0..n {
            let next = (i + 1) % n;
            f_shift_vals[i] = f_vals[next];
            t_shift_vals[i] = t_vals[next];
        }
        let mut h_vals = vec![ScalarField::ZERO; n];
        for i in 0..n {
            h_vals[i] = t_shift_vals[i] - t_vals[i] * f_shift_vals[i];
        }
        let h = interpolate(domain, &h_vals);

        let h_proof = ZeroTest::prove(kzg, &h, domain, r);

        let t_commit = kzg.commit(&t);
        let (first_eval, first_proof) = kzg.open(&t, domain[0]);

        ProductCheckProof {
            f_commit: kzg.commit(f),
            t_commit,
            h_proof,
            first_eval,
            first_proof,
            first_point: domain[0],
        }
    }

    pub fn verify(kzg: &KZG10, domain: &[ScalarField], proof: &ProductCheckProof) -> bool {
        if !ZeroTest::verify(kzg, domain, &proof.h_proof) {
            return false;
        }
        if !kzg.verify(
            &proof.t_commit,
            proof.first_point,
            proof.first_eval,
            &proof.first_proof,
        ) {
            return false;
        }
        proof.first_eval == ScalarField::ONE
    }
}

type PrescribedPermutationProof = ProductCheckProof;

pub struct PrescribedPermutationCheck;

impl PrescribedPermutationCheck {
    // Prove that f(y) = g(W(y)) for all y in domain via a product check:
    // a_i = f(y_i) / g(W(y_i)), then prove ∏ a_i = 1.
    pub fn prove(
        kzg: &KZG10,
        f: &DensePolynomial<ScalarField>,
        g: &DensePolynomial<ScalarField>,
        domain: &[ScalarField],
        w_values: &[ScalarField],
        r: ScalarField,
    ) -> PrescribedPermutationProof {
        assert_eq!(domain.len(), w_values.len());
        let n = domain.len();
        let mut a_vals = Vec::with_capacity(n);
        for i in 0..n {
            let y = domain[i];
            let wy = w_values[i];
            let fv = f.evaluate(&y);
            let gv = g.evaluate(&wy);
            a_vals.push(fv * gv.inverse().unwrap());
        }
        let a = interpolate(domain, &a_vals);
        let product_proof = ProductCheck::prove(kzg, &a, domain, r);
        product_proof
    }

    pub fn verify(kzg: &KZG10, domain: &[ScalarField], proof: &PrescribedPermutationProof) -> bool {
        ProductCheck::verify(kzg, domain, &proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_test_prove_verify() {
        let kzg = KZG10::setup(8, ScalarField::from(5u64));
        let domain = linear_domain(4, 1);
        let z = vanishing_poly(&domain);
        let q = DensePolynomial::from_coefficients_vec(vec![
            ScalarField::from(2u64),
            ScalarField::from(3u64),
        ]);
        let f = &q * &z;
        let r = ScalarField::from(7u64);
        let proof = ZeroTest::prove(&kzg, &f, &domain, r);
        assert!(ZeroTest::verify(&kzg, &domain, &proof));

        let mut false_proof = proof;
        false_proof.r = ScalarField::from(6u64);
        assert!(!ZeroTest::verify(&kzg, &domain, &false_proof));
    }

    #[test]
    fn test_product_check_prove_verify() {
        let kzg = KZG10::setup(8, ScalarField::from(5u64));
        let domain = linear_domain(4, 1);
        let f_vals = vec![
            ScalarField::from(2u64),
            ScalarField::from(3u64),
            ScalarField::from(5u64),
            ScalarField::from(6u64),
        ];
        let prod = f_vals
            .iter()
            .cloned()
            .fold(ScalarField::ONE, |acc, v| acc * v);
        let inv_prod = prod.inverse().unwrap();
        let f_vals = vec![f_vals[0], f_vals[1], f_vals[2], f_vals[3] * inv_prod];
        let f = interpolate(&domain, &f_vals);
        let r = ScalarField::from(7u64);
        let proof = ProductCheck::prove(&kzg, &f, &domain, r);
        assert!(ProductCheck::verify(&kzg, &domain, &proof));

        let mut false_proof = proof;
        false_proof.first_eval = ScalarField::from(6u64);
        assert!(!ProductCheck::verify(&kzg, &domain, &false_proof));
    }

    #[test]
    fn test_prescribed_permutation_check_prove_verify_success() {
        let kzg = KZG10::setup(8, ScalarField::from(5u64));
        let domain = linear_domain(4, 1);
        let w_values = vec![domain[1], domain[2], domain[3], domain[0]];
        let g_vals = vec![
            ScalarField::from(2u64),
            ScalarField::from(4u64),
            ScalarField::from(7u64),
            ScalarField::from(8u64),
        ];
        let g = interpolate(&domain, &g_vals);
        let mut f_vals = Vec::with_capacity(domain.len());
        for i in 0..domain.len() {
            let wy = w_values[i];
            f_vals.push(g.evaluate(&wy));
        }
        let f = interpolate(&domain, &f_vals);

        let r = ScalarField::from(7u64);
        let proof = PrescribedPermutationCheck::prove(&kzg, &f, &g, &domain, &w_values, r);
        assert!(PrescribedPermutationCheck::verify(&kzg, &domain, &proof));

        let mut false_proof = proof;
        false_proof.first_eval = ScalarField::from(6u64);
        assert!(!PrescribedPermutationCheck::verify(
            &kzg,
            &domain,
            &false_proof
        ));
    }
}
