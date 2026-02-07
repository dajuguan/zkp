## Summary
> Linear PCP proves *existence* of a witness;
> Groth16 proves *knowledge* of a witness.

## Linear PCP

The verifier is only allowed to check **linear functions of the witness**.

Linear PCP satisfies:

* **completeness**
* **soundness** (information-theoretic)

However, it does **not** satisfy *knowledge soundness*:

* soundness only guarantees that **a satisfying witness exists**
* the verifier has no way to ensure that the prover **actually knows** such a witness, since the prover is modeled as an oracle

---

## Groth16 = Linear PCP + Algebraization + KoE Assumptions

Groth16 embeds the linear PCP into an algebraic group and adds the **Knowledge-of-Exponent (KoE)** assumption.

KoE informally states:

> “If you give me a group element that satisfies the pairing checks,
> then you must know the exponent of that element;
> and that exponent corresponds to a valid witness.”

Under this assumption, Groth16 satisfies:

* **completeness**
* **knowledge soundness** (i.e., it is a SNARK / argument of knowledge)
