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

fn interpolate(domain: &[ScalarField], values: &[ScalarField]) -> DensePolynomial<ScalarField> {
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

fn shift_by_omega(
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

fn mul_poly(
    a: &DensePolynomial<ScalarField>,
    b: &DensePolynomial<ScalarField>,
) -> DensePolynomial<ScalarField> {
    if a.coeffs.is_empty() || b.coeffs.is_empty() {
        return DensePolynomial::from_coefficients_vec(vec![]);
    }
    let mut coeffs = vec![ScalarField::ZERO; a.coeffs.len() + b.coeffs.len() - 1];
    for (i, &ai) in a.coeffs.iter().enumerate() {
        if ai == ScalarField::ZERO {
            continue;
        }
        for (j, &bj) in b.coeffs.iter().enumerate() {
            if bj == ScalarField::ZERO {
                continue;
            }
            coeffs[i + j] += ai * bj;
        }
    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

fn sub_poly(
    a: &DensePolynomial<ScalarField>,
    b: &DensePolynomial<ScalarField>,
) -> DensePolynomial<ScalarField> {
    let n = a.coeffs.len().max(b.coeffs.len());
    let mut coeffs = vec![ScalarField::ZERO; n];
    for i in 0..n {
        let av = a.coeffs.get(i).cloned().unwrap_or(ScalarField::ZERO);
        let bv = b.coeffs.get(i).cloned().unwrap_or(ScalarField::ZERO);
        coeffs[i] = av - bv;
    }
    DensePolynomial::from_coefficients_vec(coeffs)
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
    // prove that ∏_{x in domain} f(x) = 1.
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
        let tf = mul_poly(&t, &f_shift);
        let h = sub_poly(&t_shift, &tf);
        let z = subgroup_vanishing_poly(n);
        let (q, rem) = DenseOrSparsePolynomial::from(&h)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&z))
            .expect("division by non-zero polynomial must succeed");
        debug_assert!(rem.is_zero());

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

type PrescribedPermutationProof = ProductCheckProof;

pub struct PrescribedPermutationCheck;

impl PrescribedPermutationCheck {
    // Prove that f(x) = g(W(x)) for all x in domain via a product check:
    // f'(x) = f(x) + beta * W(x) + gama
    // g'(x) = g(x) + beta * x + gama
    // z(x) = f'/g', then prove ∏x∈Ω z(x) = 1.
    pub fn prove(
        kzg: &KZG10,
        f: &DensePolynomial<ScalarField>,
        g: &DensePolynomial<ScalarField>,
        domain: &[ScalarField],
        w_values: &[ScalarField],
        beta: ScalarField,
        gamma: ScalarField,
        r: ScalarField,
    ) -> PrescribedPermutationProof {
        assert_eq!(domain.len(), w_values.len());
        let n = domain.len();
        let mut a_vals = Vec::with_capacity(n);
        for i in 0..n {
            let y = domain[i];
            let wy = w_values[i];
            let fp = f.evaluate(&y) + beta * wy + gamma;
            let gp = g.evaluate(&y) + beta * y + gamma;
            a_vals.push(fp * gp.inverse().unwrap());
        }
        let z = interpolate(domain, &a_vals);
        let product_proof = ProductCheck::prove(kzg, &z, domain, r);
        product_proof
    }

    pub fn verify(kzg: &KZG10, domain: &[ScalarField], proof: &PrescribedPermutationProof) -> bool {
        ProductCheck::verify(kzg, domain, &proof)
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
        assert!(ZeroTest::verify(&kzg, &domain, &proof));

        let mut false_proof = proof;
        false_proof.r = ScalarField::from(6u64);
        assert!(!ZeroTest::verify(&kzg, &domain, &false_proof));
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
        let proof =
            PrescribedPermutationCheck::prove(&kzg, &f, &g, &domain, &w_values, beta, gamma, r);
        assert!(PrescribedPermutationCheck::verify(&kzg, &domain, &proof));

        let mut false_proof = proof;
        false_proof.last_eval = ScalarField::from(6u64);
        assert!(!PrescribedPermutationCheck::verify(
            &kzg,
            &domain,
            &false_proof
        ));
    }
}
