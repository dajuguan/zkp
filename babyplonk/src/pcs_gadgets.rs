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

pub fn multiplicative_domain(n: usize, omega: ScalarField) -> Vec<ScalarField> {
    if n == 0 {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(n);
    let mut cur = ScalarField::ONE;
    for _ in 0..n {
        out.push(cur);
        cur *= omega;
    }
    out
}

fn vanishing_poly(domain: &[ScalarField]) -> DensePolynomial<ScalarField> {
    let mut poly = DensePolynomial::from_coefficients_vec(vec![ScalarField::ONE]);
    for &x in domain {
        let factor = DensePolynomial::from_coefficients_vec(vec![-x, ScalarField::ONE]);
        poly = &poly * &factor;
    }
    poly
}

fn subgroup_vanishing_poly(n: usize) -> DensePolynomial<ScalarField> {
    if n == 0 {
        return DensePolynomial::from_coefficients_vec(vec![ScalarField::ONE]);
    }
    let mut coeffs = vec![ScalarField::ZERO; n + 1];
    coeffs[0] = -ScalarField::ONE;
    coeffs[n] = ScalarField::ONE;
    DensePolynomial::from_coefficients_vec(coeffs)
}

pub fn interpolate(domain: &[ScalarField], values: &[ScalarField]) -> DensePolynomial<ScalarField> {
    assert_eq!(domain.len(), values.len());
    let n = domain.len();
    let mut acc = vec![ScalarField::ZERO];

    for i in 0..n {
        let mut num = vec![ScalarField::ONE];
        let mut den = ScalarField::ONE;
        for j in 0..n {
            if i == j {
                continue;
            }
            let factor = vec![-domain[j], ScalarField::ONE];
            let mut next = vec![ScalarField::ZERO; num.len() + 1];
            for (a, coeff_a) in num.iter().enumerate() {
                next[a] += *coeff_a * factor[0];
                next[a + 1] += *coeff_a * factor[1];
            }
            num = next;
            den *= domain[i] - domain[j];
        }
        let scale = values[i] * den.inverse().unwrap();
        if acc.len() < num.len() {
            acc.resize(num.len(), ScalarField::ZERO);
        }
        for (k, coeff) in num.iter().enumerate() {
            acc[k] += *coeff * scale;
        }
    }

    DensePolynomial::from_coefficients_vec(acc)
}

pub fn shift_by_omega(
    poly: &DensePolynomial<ScalarField>,
    omega: ScalarField,
) -> DensePolynomial<ScalarField> {
    let mut coeffs = poly.coeffs.clone();
    let mut pow = ScalarField::ONE;
    for coeff in coeffs.iter_mut() {
        *coeff *= pow;
        pow *= omega;
    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

pub struct ZeroTestProof {
    pub q_commit: G1Point,
    pub r: ScalarField,
    pub q_eval: ScalarField,
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

        let q_commit = kzg.commit(&q);

        let (q_eval, q_proof) = kzg.open(&q, r);

        ZeroTestProof {
            q_commit,
            r,
            q_eval,
            q_proof,
        }
    }

    pub fn verify_with_f_eval(
        kzg: &KZG10,
        domain: &[ScalarField],
        f_eval: ScalarField,
        proof: &ZeroTestProof,
    ) -> bool {
        let z = vanishing_poly(domain);
        let z_r = z.evaluate(&proof.r);
        if !kzg.verify(&proof.q_commit, proof.r, proof.q_eval, &proof.q_proof) {
            return false;
        }
        f_eval == proof.q_eval * z_r
    }

    pub fn verify_with_poly(
        kzg: &KZG10,
        domain: &[ScalarField],
        f: &DensePolynomial<ScalarField>,
        proof: &ZeroTestProof,
    ) -> bool {
        let f_eval = f.evaluate(&proof.r);
        Self::verify_with_f_eval(kzg, domain, f_eval, proof)
    }
}

pub struct ProductCheckProof {
    pub f_commit: G1Point,
    pub t_commit: G1Point,
    pub q_commit: G1Point,
    pub last_eval: ScalarField,
    pub last_proof: G1Point,
    pub last_point: ScalarField,
    pub r: ScalarField,
    pub t_eval_r: ScalarField,
    pub t_proof_r: G1Point,
    pub t_eval_wr: ScalarField,
    pub t_proof_wr: G1Point,
    pub f_eval_wr: ScalarField,
    pub f_proof_wr: G1Point,
    pub q_eval_r: ScalarField,
    pub q_proof_r: G1Point,
    pub omega: ScalarField,
}

pub struct ProductCheck;

impl ProductCheck {
    // Product check on multiplicative subgroup domain 1, ω, ω^2, ...:
    // prove that ∏_{x in domain} a(x) = 1.
    //  1. 𝑡 (𝜔 ⋅ x) − 𝑡 (𝑥 )⋅ a (𝜔 ⋅ x) = 0
    //  2. 𝑡(𝜔^(𝑘−1)) = 1
    //  t_eval_wr - t_eval_r * a_eval_wr == q_eval_r * z_r
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
        #[cfg(test)]
        for (i, &x) in domain.iter().enumerate() {
            if f.evaluate(&x) != f_vals[i] {
                eprintln!("product_check: f eval mismatch at x={:?}", x);
            }
        }

        let mut t_vals = vec![ScalarField::ZERO; n];
        if n > 0 {
            t_vals[0] = f_vals[0];
            for i in 1..n {
                t_vals[i] = t_vals[i - 1] * f_vals[i];
            }
        }

        let t = interpolate(domain, &t_vals);

        let omega = if n > 1 {
            domain[1] * domain[0].inverse().unwrap()
        } else {
            ScalarField::ONE
        };
        let t_shift = shift_by_omega(&t, omega);
        let f_shift = shift_by_omega(f, omega);
        let tf = &t * &f_shift;
        let h = &t_shift - &tf;
        let z = subgroup_vanishing_poly(n);
        let (q, rem) = DenseOrSparsePolynomial::from(&h)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&z))
            .expect("division by non-zero polynomial must succeed");
        let _ = rem;

        let t_commit = kzg.commit(&t);
        let q_commit = kzg.commit(&q);
        let last_point = domain[n - 1];
        let (last_eval, last_proof) = kzg.open(&t, last_point);

        let wr = r * omega;
        let (t_eval_r, t_proof_r) = kzg.open(&t, r);
        let (t_eval_wr, t_proof_wr) = kzg.open(&t, wr);
        let (f_eval_wr, f_proof_wr) = kzg.open(f, wr);
        let (q_eval_r, q_proof_r) = kzg.open(&q, r);

        ProductCheckProof {
            f_commit: kzg.commit(f),
            t_commit,
            q_commit,
            last_eval,
            last_proof,
            last_point,
            r,
            t_eval_r,
            t_proof_r,
            t_eval_wr,
            t_proof_wr,
            f_eval_wr,
            f_proof_wr,
            q_eval_r,
            q_proof_r,
            omega,
        }
    }

    pub fn verify(kzg: &KZG10, domain: &[ScalarField], proof: &ProductCheckProof) -> bool {
        if !kzg.verify(
            &proof.t_commit,
            proof.last_point,
            proof.last_eval,
            &proof.last_proof,
        ) {
            return false;
        }
        if proof.last_eval != ScalarField::ONE {
            return false;
        }
        let r = proof.r;
        let wr = r * proof.omega;
        if !kzg.verify(&proof.t_commit, r, proof.t_eval_r, &proof.t_proof_r) {
            return false;
        }
        if !kzg.verify(&proof.t_commit, wr, proof.t_eval_wr, &proof.t_proof_wr) {
            return false;
        }
        if !kzg.verify(&proof.f_commit, wr, proof.f_eval_wr, &proof.f_proof_wr) {
            return false;
        }
        if !kzg.verify(&proof.q_commit, r, proof.q_eval_r, &proof.q_proof_r) {
            return false;
        }
        let z = subgroup_vanishing_poly(domain.len());
        let z_r = z.evaluate(&r);
        proof.t_eval_wr - proof.t_eval_r * proof.f_eval_wr == proof.q_eval_r * z_r
    }
}

pub struct PrescribedPermutationProof {
    pub f_commit: G1Point,
    pub g_commit: G1Point,
    pub z_commit: G1Point,
    pub q_commit: G1Point,
    pub r: ScalarField,
    // proof at r
    pub f_eval_r: ScalarField,
    pub f_proof_r: G1Point,
    pub g_eval_r: ScalarField,
    pub g_proof_r: G1Point,
    pub z_eval_r: ScalarField,
    pub z_proof_r: G1Point,
    pub q_eval_r: ScalarField,
    pub q_proof_r: G1Point,
    // proof at wr
    pub z_eval_wr: ScalarField,
    pub z_proof_wr: G1Point,
}

pub struct PrescribedPermutationCheck;

// ref: https://github.com/sec-bit/learning-zkp/blob/master/plonk-intro-zh/3-plonk-permutation.md
impl PrescribedPermutationCheck {
    // Prove that f(x) = g(W(x)) for all x in domain via a product check:
    // f'(x) = f(x) + beta * W(x) + gamma
    // g'(x) = g(x) + beta * x + gamma
    // z(w x) / z(x) = f'(x) / g'(x), with z(w^{n-1}) = 1
    // h(x) = l_k(x) * (z(x) - 1) + alpha * (z(w x) g'(x) - z(x) f'(x))
    pub fn prove(
        kzg: &KZG10,
        f: &DensePolynomial<ScalarField>,
        g: &DensePolynomial<ScalarField>,
        domain: &[ScalarField],
        w_values: &[ScalarField],
        alpha: ScalarField,
        beta: ScalarField,
        gamma: ScalarField,
        r: ScalarField,
    ) -> PrescribedPermutationProof {
        assert_eq!(domain.len(), w_values.len());
        let omega = domain[1] / domain[0];
        let n = domain.len();
        let mut z_vals = Vec::with_capacity(n);
        if n > 0 {
            z_vals.push(ScalarField::ONE);
        }
        for i in 0..n.saturating_sub(1) {
            let y = domain[i];
            let wy = w_values[i];
            let fv = f.evaluate(&y);
            let gv = g.evaluate(&y);
            let fp = fv + beta * wy + gamma;
            let gp = gv + beta * y + gamma;
            let next = *z_vals.last().unwrap() * fp * gp.inverse().unwrap();
            z_vals.push(next);
        }
        let z = interpolate(domain, &z_vals);
        let z_commit = kzg.commit(&z);
        let (z_eval_r, z_proof_r) = kzg.open(&z, r);
        let (z_eval_wr, z_proof_wr) = kzg.open(&z, omega * r);

        let mut l_k_vals = vec![ScalarField::ZERO; n];
        if n > 0 {
            l_k_vals[0] = ScalarField::ONE;
        }

        // random linear combination for product check and boundary check
        let l_k = interpolate(domain, &l_k_vals);
        let zw = shift_by_omega(&z, omega);
        let w_poly = interpolate(domain, w_values);
        let ff = f + &DensePolynomial::from_coefficients_slice(&[gamma]) + &w_poly * beta;
        let gg = g + &DensePolynomial::from_coefficients_slice(&[gamma, beta]);
        let h = l_k
            .naive_mul(&(&z - &DensePolynomial::from_coefficients_slice(&[ScalarField::ONE])))
            + &(&(zw.naive_mul(&gg)) - &(z.naive_mul(&ff))) * alpha;

        // quotient poly
        let t = subgroup_vanishing_poly(n);
        let (q, rem) = DenseOrSparsePolynomial::from(&h)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&t))
            .expect("division by non-zero polynomial must succeed");

        let q_commit = kzg.commit(&q);
        let (q_eval_r, q_proof_r) = kzg.open(&q, r);

        let f_commit = kzg.commit(f);
        let g_commit = kzg.commit(g);
        let (f_eval_r, f_proof_r) = kzg.open(f, r);
        let (g_eval_r, g_proof_r) = kzg.open(g, r);

        PrescribedPermutationProof {
            f_commit,
            g_commit,
            z_commit,
            q_commit,
            r,
            // evaluation at r
            f_eval_r,
            f_proof_r,
            g_eval_r,
            g_proof_r,
            z_eval_r,
            z_proof_r,
            q_eval_r,
            q_proof_r,
            // proof at wr
            z_eval_wr,
            z_proof_wr,
        }
    }

    pub fn verify(
        kzg: &KZG10,
        domain: &[ScalarField],
        w_values: &[ScalarField],
        alpha: ScalarField,
        beta: ScalarField,
        gamma: ScalarField,
        r: ScalarField,
        proof: &PrescribedPermutationProof,
    ) -> bool {
        if proof.r != r {
            return false;
        }
        if domain.len() < 2 {
            return false;
        }
        if !kzg.verify(&proof.f_commit, r, proof.f_eval_r, &proof.f_proof_r) {
            return false;
        }
        if !kzg.verify(&proof.g_commit, r, proof.g_eval_r, &proof.g_proof_r) {
            return false;
        }
        if !kzg.verify(&proof.z_commit, r, proof.z_eval_r, &proof.z_proof_r) {
            return false;
        }
        let omega = domain[1] / domain[0];
        let wr = r * omega;
        if !kzg.verify(&proof.z_commit, wr, proof.z_eval_wr, &proof.z_proof_wr) {
            return false;
        }
        if !kzg.verify(&proof.q_commit, r, proof.q_eval_r, &proof.q_proof_r) {
            return false;
        }

        let n = domain.len();
        let w_poly = interpolate(domain, w_values);
        let w_eval_r = w_poly.evaluate(&r);

        let f_prime_r = proof.f_eval_r + beta * w_eval_r + gamma;
        let g_prime_r = proof.g_eval_r + beta * r + gamma;

        let mut l_k_vals = vec![ScalarField::ZERO; n];
        if n > 0 {
            l_k_vals[0] = ScalarField::ONE;
        }
        let l_k = interpolate(domain, &l_k_vals);
        let l_k_r = l_k.evaluate(&r);

        let h_r = l_k_r * (proof.z_eval_r - ScalarField::ONE)
            + alpha * (proof.z_eval_wr * g_prime_r - proof.z_eval_r * f_prime_r);
        let z_h = subgroup_vanishing_poly(n);
        let z_h_r = z_h.evaluate(&r);
        h_r == proof.q_eval_r * z_h_r
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::UniformRand;
    use ark_std::test_rng;

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
        let mut rng = test_rng();
        let r = ScalarField::rand(&mut rng);
        let proof = ZeroTest::prove(&kzg, &f, &domain, r);
        assert!(ZeroTest::verify_with_poly(&kzg, &domain, &f, &proof));

        let mut false_proof = proof;
        false_proof.q_eval = false_proof.q_eval + ScalarField::from(1u64);
        assert!(!ZeroTest::verify_with_poly(&kzg, &domain, &f, &false_proof));
    }

    #[test]
    fn test_product_check_prove_verify() {
        let kzg = KZG10::setup(8, ScalarField::from(5u64));
        let omega = ScalarField::from(4u64);
        let domain = multiplicative_domain(4, omega);
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
        let mut rng = test_rng();
        let r = ScalarField::rand(&mut rng);
        let proof = ProductCheck::prove(&kzg, &f, &domain, r);
        assert!(ProductCheck::verify(&kzg, &domain, &proof));

        let mut false_proof = proof;
        false_proof.last_eval = ScalarField::from(6u64);
        assert!(!ProductCheck::verify(&kzg, &domain, &false_proof));
    }

    #[test]
    fn test_prescribed_permutation_check_prove_verify_success() {
        let kzg = KZG10::setup(8, ScalarField::from(5u64));
        let omega = ScalarField::from(4u64);
        let domain = multiplicative_domain(4, omega);
        let w_values = vec![domain[3], domain[1], domain[2], domain[0]];
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

        let mut rng = test_rng();
        let r = ScalarField::rand(&mut rng);
        let (beta, gamma) = loop {
            let beta = ScalarField::rand(&mut rng);
            let gamma = ScalarField::rand(&mut rng);
            let ok = domain
                .iter()
                .all(|y| g.evaluate(y) + beta * (*y) + gamma != ScalarField::ZERO);
            if ok {
                break (beta, gamma);
            }
        };
        let alpha = ScalarField::rand(&mut rng);
        let proof = PrescribedPermutationCheck::prove(
            &kzg, &f, &g, &domain, &w_values, alpha, beta, gamma, r,
        );
        assert!(PrescribedPermutationCheck::verify(
            &kzg, &domain, &w_values, alpha, beta, gamma, r, &proof
        ));

        let mut false_proof = proof;
        false_proof.q_eval_r = false_proof.q_eval_r + ScalarField::from(1u64);
        assert!(!PrescribedPermutationCheck::verify(
            &kzg,
            &domain,
            &w_values,
            alpha,
            beta,
            gamma,
            r,
            &false_proof
        ));
    }
}
