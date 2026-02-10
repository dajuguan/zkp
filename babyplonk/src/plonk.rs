use crate::{
    kzg::{KZG10, PolyCommit},
    pcs_gadgets::{
        PrescribedPermutationCheck, PrescribedPermutationProof, find_root_of_unity, interpolate,
        multiplicative_domain, shift_by_omega,
    },
    tiny_field::{G1Point, ScalarField},
};
use ark_ff::{Field, UniformRand};
use ark_poly::{
    DenseUVPolynomial, Polynomial,
    univariate::{DenseOrSparsePolynomial, DensePolynomial},
};
use ark_std::test_rng;

#[derive(Debug, Clone)]
pub struct Plonk<Fr, PCS: PolyCommit> {
    witness: Vec<Fr>,
    selector: Vec<Fr>,
    perm: Vec<u64>,
    pcs: PCS,
    omega: Fr,
}

pub struct PlonkKZG10Proof {
    gate_proof: GateCheckProof,
    wire_proof: PrescribedPermutationProof,
    t_eval_wr: ScalarField,
    t_proof_wr: G1Point,
    t_eval_w2r: ScalarField,
    t_proof_w2r: G1Point,
}

pub struct GateCheckProof {
    pub q_commit: G1Point,
    pub r: ScalarField,
    pub q_eval_r: ScalarField,
    pub q_proof_r: G1Point,
}

impl Plonk<ScalarField, KZG10> {
    pub fn new(witness: Vec<ScalarField>, selector: Vec<ScalarField>, perm: Vec<u64>) -> Self {
        assert!(
            witness.len() >= selector.len() * 3,
            "witness length must be at least 3 * selector length"
        );
        assert!(
            witness.len() == perm.len(),
            "witness and permuation len doesn't match!"
        );
        let mut rng = test_rng();
        // tau is unknown for both prover and verifier
        let tau = ScalarField::rand(&mut rng);
        let pcs = KZG10::setup(witness.len() * 3, tau);
        let omega = find_root_of_unity(perm.len());
        Self {
            witness,
            selector,
            perm,
            pcs,
            omega,
        }
    }

    pub fn prove(
        &self,
        r: ScalarField,
        alpha: ScalarField,
        beta: ScalarField,
        gamma: ScalarField,
    ) -> PlonkKZG10Proof {
        // Gate constraint over Ω_gates:
        //   S(y) * (T(y) + T(ωy)) + (1 - S(y)) * T(y) * T(ωy) - T(ω^2 y) = 0, ∀ y ∈ Ω_gates.
        // Permutation constraint over Ω:
        // T(y) = T(W(y))  (checked via prescribed permutation with α, β, γ).
        // T(x): witness polynomial over Ω;
        // S(x): selector polynomial over Ω_gates;
        // W(x): permutation polynomial given by perm indices over Ω.
        // commit T
        let witness = &self.witness;
        let selector = &self.selector;
        let perm = &self.perm;
        let pcs = &self.pcs;
        let omega = self.omega;
        let t_domain = multiplicative_domain(witness.len(), omega);

        // encode & commit witness
        // T(x): interpolate witness values over Ω.
        let t_poly = interpolate(&t_domain, &self.witness);
        // Open T(x) at ωr, ω^2 r for the gate constraint (T(r) comes from wire_proof).
        let omega_r = r * omega;
        let omega2_r = r * omega * omega;
        let (t_eval_wr, t_proof_wr) = pcs.open(&t_poly, omega_r);
        let (t_eval_w2r, t_proof_w2r) = pcs.open(&t_poly, omega2_r);

        // Gate domain: {1, ω^3, ω^6, ...} with size = selector.len().
        // IMPORTANT: build gate_poly by formula, not by interpolating a few gate_domain samples,
        // because the true gate polynomial degree can exceed the gate_domain size.
        let gate_domain = multiplicative_domain(selector.len(), omega * omega * omega);
        // S(x): selector over Ω_gates; T(ωx), T(ω^2 x) are shifted polynomials.
        let s_poly = interpolate(&gate_domain, &selector);
        let t_omega = shift_by_omega(&t_poly, omega);
        let t_omega2 = shift_by_omega(&t_poly, omega * omega);
        let one = DensePolynomial::from_coefficients_vec(vec![ScalarField::ONE]);
        let one_minus_s = &one - &s_poly;
        // G(x): gate polynomial constructed by formula (not by interpolating samples).
        let mut gate_poly = s_poly.naive_mul(&(&t_poly + &t_omega));
        gate_poly += &one_minus_s.naive_mul(&t_poly.naive_mul(&t_omega));
        gate_poly += &(-t_omega2);
        let mut gate_coeffs = gate_poly.coeffs.clone();
        while let Some(true) = gate_coeffs.last().map(|c| *c == ScalarField::ZERO) {
            gate_coeffs.pop();
        }
        let gate_poly = DensePolynomial::from_coefficients_vec(gate_coeffs);
        // Z_gates(x): vanishing polynomial of Ω_gates.
        let z_gate = vanishing_poly(&gate_domain);
        let (q, _rem) = DenseOrSparsePolynomial::from(&gate_poly)
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(&z_gate))
            .expect("division by non-zero polynomial must succeed");
        let q_commit = pcs.commit(&q);
        let (q_eval_r, q_proof_r) = pcs.open(&q, r);
        let gate_proof = GateCheckProof {
            q_commit,
            r,
            q_eval_r,
            q_proof_r,
        };

        // Wires prescribed permutation check (T vs. T(W)).
        let mut tw_evals = Vec::with_capacity(witness.len());
        for i in 0..witness.len() {
            let eval = witness[perm[i] as usize];
            tw_evals.push(eval);
        }
        let tw_poly = interpolate(&t_domain, &tw_evals);
        // W(x): permutation polynomial as values over Ω.
        let w_values: Vec<_> = perm.iter().map(|v| t_domain[*v as usize]).collect();
        let wire_proof = PrescribedPermutationCheck::prove(
            pcs, &t_poly, &tw_poly, &t_domain, &w_values, alpha, beta, gamma, r,
        );

        PlonkKZG10Proof {
            gate_proof,
            wire_proof,
            t_eval_wr,
            t_proof_wr,
            t_eval_w2r,
            t_proof_w2r,
        }
    }

    pub fn verify(
        &self,
        proof: &PlonkKZG10Proof,
        r: ScalarField,
        alpha: ScalarField,
        beta: ScalarField,
        gamma: ScalarField,
    ) -> bool {
        // Verify at random r:
        //   S(r) * (T(r) + T(ωr)) + (1 - S(r)) * T(r) * T(ωr) - T(ω^2 r) = Q_gate(r) * Z_gates(r).
        // And verify the prescribed permutation check for T against W.
        // T(x): witness polynomial over Ω;
        // S(x): selector polynomial over Ω_gates;
        // W(x): permutation polynomial defined by perm indices over Ω.
        let witness_len = self.perm.len();
        let omega = self.omega;
        let t_domain = multiplicative_domain(witness_len, omega);
        let gate_domain = multiplicative_domain(self.selector.len(), omega * omega * omega);

        if gate_domain.contains(&r) {
            return false;
        }
        if proof.gate_proof.r != r {
            return false;
        }
        if proof.wire_proof.r != r {
            return false;
        }
        let omega_r = r * omega;
        let omega2_r = r * omega * omega;
        // T(r) is provided by wire_proof (f = T in permutation check).
        let t_eval_r = proof.wire_proof.f_eval_r;
        let t_eval_wr;
        let t_eval_w2r;
        // T(ωr) and T(ω^2 r) are verified against the same commitment from wire_proof.
        if !self.pcs.verify(
            &proof.wire_proof.f_commit,
            omega_r,
            proof.t_eval_wr,
            &proof.t_proof_wr,
        ) {
            return false;
        } else {
            t_eval_wr = proof.t_eval_wr;
        }
        if !self.pcs.verify(
            &proof.wire_proof.f_commit,
            omega2_r,
            proof.t_eval_w2r,
            &proof.t_proof_w2r,
        ) {
            return false;
        } else {
            t_eval_w2r = proof.t_eval_w2r;
        }
        let s_poly = interpolate(&gate_domain, &self.selector);
        let s_eval = s_poly.evaluate(&r);
        let gate_eval_r = s_eval * (t_eval_r + t_eval_wr)
            + (ScalarField::ONE - s_eval) * t_eval_r * t_eval_wr
            - t_eval_w2r;
        // Z_gates(r): vanishing polynomial of Ω_gates evaluated at r.
        let mut z_gate_eval_r = ScalarField::ONE;
        for x in gate_domain.iter() {
            z_gate_eval_r *= r - *x;
        }
        if z_gate_eval_r == ScalarField::ZERO {
            return false;
        }
        if gate_eval_r != proof.gate_proof.q_eval_r * z_gate_eval_r {
            return false;
        }
        if !self.pcs.verify(
            &proof.gate_proof.q_commit,
            r,
            proof.gate_proof.q_eval_r,
            &proof.gate_proof.q_proof_r,
        ) {
            #[cfg(test)]
            eprintln!("verify fail: gate q open");
            return false;
        }

        let _ = alpha;
        let w_values: Vec<_> = self.perm.iter().map(|v| t_domain[*v as usize]).collect();
        if !PrescribedPermutationCheck::verify(
            &self.pcs,
            &t_domain,
            &w_values,
            alpha,
            beta,
            gamma,
            r,
            &proof.wire_proof,
        ) {
            return false;
        }
        // alpha/beta/gamma are only used to construct the permutation proof; no additional checks here.
        let _ = (alpha, beta, gamma);
        true
    }
}

fn vanishing_poly(domain: &[ScalarField]) -> DensePolynomial<ScalarField> {
    let mut coeffs = vec![ScalarField::ONE];
    for &x in domain {
        let factor = vec![-x, ScalarField::ONE];
        coeffs = poly_mul_coeffs(&coeffs, &factor);
    }
    DensePolynomial::from_coefficients_vec(coeffs)
}

fn poly_mul_coeffs(a: &[ScalarField], b: &[ScalarField]) -> Vec<ScalarField> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut out = vec![ScalarField::ZERO; a.len() + b.len() - 1];
    for (i, ai) in a.iter().enumerate() {
        for (j, bj) in b.iter().enumerate() {
            out[i + j] += *ai * *bj;
        }
    }
    while let Some(true) = out.last().map(|c| *c == ScalarField::ZERO) {
        out.pop();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_poly::Polynomial;

    #[test]
    fn test_minimal_plonk_add_mul() {
        // domain size 8 (divides 16), 2 gates -> 6 wire values + 2 padding
        let witness = vec![
            ScalarField::from(2u64),  // a
            ScalarField::from(3u64),  // b
            ScalarField::from(5u64),  // c = a + b
            ScalarField::from(5u64),  // d = c
            ScalarField::from(4u64),  // e
            ScalarField::from(20u64), // f = d * e = 20
            ScalarField::ZERO,
            ScalarField::ZERO,
        ];
        // selector on gate domain: [1 (add), 0 (mul)]
        let selector = vec![ScalarField::ONE, ScalarField::ZERO];
        // identity permutation over 8 points
        let mut perm: Vec<u64> = (0..witness.len() as u64).collect();
        perm[2] = 3;
        perm[3] = 2;

        let plonk = Plonk::new(witness.clone(), selector.clone(), perm.clone());
        let mut rng = test_rng();
        let t_domain = multiplicative_domain(witness.len(), plonk.omega);
        let gate_domain =
            multiplicative_domain(selector.len(), plonk.omega * plonk.omega * plonk.omega);
        let r = loop {
            let candidate = ScalarField::rand(&mut rng);
            if !t_domain.contains(&candidate) && !gate_domain.contains(&candidate) {
                break candidate;
            }
        };
        let (beta, gamma) = loop {
            let beta = ScalarField::rand(&mut rng);
            let gamma = ScalarField::rand(&mut rng);
            let ok = (0..witness.len()).all(|i| {
                let y = t_domain[i];
                let gv = witness[perm[i] as usize];
                gv + beta * y + gamma != ScalarField::ZERO
            });
            if ok {
                break (beta, gamma);
            }
        };
        let alpha = ScalarField::rand(&mut rng);

        let proof = plonk.prove(r, alpha, beta, gamma);
        assert!(plonk.verify(&proof, r, alpha, beta, gamma));

        // creat a fake witness for add gate, should fail!
        let mut plonk_fake_add_gate_witness = plonk.clone();
        plonk_fake_add_gate_witness.witness[0] = ScalarField::ONE;
        let proof = plonk_fake_add_gate_witness.prove(r, alpha, beta, gamma);
        assert!(!plonk.verify(&proof, r, alpha, beta, gamma));

        // creat a fake witness for mul gate, should fail!
        let mut plonk_fake_mul_gate_witness = plonk.clone();
        plonk_fake_mul_gate_witness.witness[5] = ScalarField::from(2u64);
        let proof = plonk_fake_mul_gate_witness.prove(r, alpha, beta, gamma);
        assert!(!plonk.verify(&proof, r, alpha, beta, gamma));

        // creat a fake selector for add gate, should fail!
        let mut plonk_fake_add_gate_selector = plonk.clone();
        plonk_fake_add_gate_selector.selector[0] = ScalarField::ZERO;
        let proof = plonk_fake_add_gate_selector.prove(r, alpha, beta, gamma);
        assert!(!plonk.verify(&proof, r, alpha, beta, gamma));

        // creat a fake selector for mul gate, should fail!
        let mut plonk_fake_add_gate_selector = plonk.clone();
        plonk_fake_add_gate_selector.selector[1] = ScalarField::ONE;
        let proof = plonk_fake_add_gate_selector.prove(r, alpha, beta, gamma);
        assert!(!plonk.verify(&proof, r, alpha, beta, gamma));

        // creat a fake perm, should fail!
        let mut plonk_fake_perm = plonk.clone();
        plonk_fake_perm.perm[5] = 1;
        let proof = plonk_fake_perm.prove(r, alpha, beta, gamma);
        assert!(!plonk.verify(&proof, r, alpha, beta, gamma));
    }

    #[test]
    fn test_tw_poly_identity_mapping() {
        let witness = vec![
            ScalarField::from(2u64),
            ScalarField::from(20u64),
            ScalarField::from(5u64),
            ScalarField::from(4u64),
            ScalarField::from(5u64),
            ScalarField::from(20u64),
            ScalarField::ZERO,
            ScalarField::ZERO,
        ];
        let selector = vec![ScalarField::ONE, ScalarField::ZERO];
        let perm: Vec<u64> = (0..witness.len() as u64).collect();
        let plonk = Plonk::new(witness, selector, perm);

        let omega = plonk.omega;
        let t_domain = multiplicative_domain(plonk.perm.len(), omega);
        let t_poly = interpolate(&t_domain, &plonk.witness);
        let tw_poly = t_poly.clone();
        for y in t_domain.iter() {
            assert_eq!(t_poly.evaluate(y), tw_poly.evaluate(y));
        }
        let mut rng = test_rng();
        let _ = loop {
            let beta = ScalarField::rand(&mut rng);
            let gamma = ScalarField::rand(&mut rng);
            let ok = t_domain
                .iter()
                .all(|y| tw_poly.evaluate(y) + beta * (*y) + gamma != ScalarField::ZERO);
            if ok {
                break (beta, gamma);
            }
        };
    }

    #[test]
    fn test_gate_eval_openings_match_gate_poly() {
        let witness = vec![
            ScalarField::from(2u64),
            ScalarField::from(3u64),
            ScalarField::from(5u64),
            ScalarField::from(4u64),
            ScalarField::from(5u64),
            ScalarField::from(3u64),
            ScalarField::ZERO,
            ScalarField::ZERO,
        ];
        let selector = vec![ScalarField::ONE, ScalarField::ZERO];
        let perm: Vec<u64> = (0..witness.len() as u64).collect();

        let plonk = Plonk::new(witness, selector, perm);
        let mut rng = test_rng();
        let r = ScalarField::rand(&mut rng);
        let omega = plonk.omega;
        let t_domain = multiplicative_domain(plonk.perm.len(), omega);
        let t_poly = interpolate(&t_domain, &plonk.witness);
        let tw_poly = t_poly.clone();
        let (beta, gamma) = loop {
            let beta = ScalarField::rand(&mut rng);
            let gamma = ScalarField::rand(&mut rng);
            let ok = t_domain
                .iter()
                .all(|y| tw_poly.evaluate(y) + beta * (*y) + gamma != ScalarField::ZERO);
            if ok {
                break (beta, gamma);
            }
        };
        let alpha = ScalarField::rand(&mut rng);
        let proof = plonk.prove(r, alpha, beta, gamma);

        let gate_domain = multiplicative_domain(plonk.selector.len(), omega * omega * omega);
        let s_poly = interpolate(&gate_domain, &plonk.selector);
        // IMPORTANT: build gate_poly by formula, not by interpolating a few gate_domain samples,
        // because the true gate polynomial degree can exceed the gate_domain size.
        let t_w = shift_by_omega(&t_poly, omega);
        let t_w2 = shift_by_omega(&t_poly, omega * omega);
        let one = DensePolynomial::from_coefficients_vec(vec![ScalarField::ONE]);
        let one_minus_s = &one - &s_poly;
        let mut gate_poly = s_poly.naive_mul(&(&t_poly + &t_w));
        gate_poly += &one_minus_s.naive_mul(&t_poly.naive_mul(&t_w));
        gate_poly += &(-t_w2);
        let gate_eval_poly = gate_poly.evaluate(&r);
        let gate_eval_open = {
            let s_eval = s_poly.evaluate(&r);
            s_eval * (proof.wire_proof.f_eval_r + proof.t_eval_wr)
                + (ScalarField::ONE - s_eval)
                    * proof.wire_proof.f_eval_r
                    * proof.t_eval_wr
                - proof.t_eval_w2r
        };
        assert_eq!(gate_eval_poly, gate_eval_open);
    }
}
