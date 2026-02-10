# Simplication
- omit public input/output constraints
- use a simple RNG instead of Fiat-Shamir for challenges
- use single, unsplit T(x) and Sigma(x) polynomials
- use multiplicative subgroup domains for product/permutation checks
- reuse T(x) commitment and openings across checks; avoid committing auxiliary polynomials (e.g., derive h(x) then only commit q(x))
- gate constraint is verified at a single random point r (no extra points)
- use beta/gamma random linearization in the prescribed permutation check
- use naive polynomial multiplication (FFT root of unity is not valid in this tiny field)
