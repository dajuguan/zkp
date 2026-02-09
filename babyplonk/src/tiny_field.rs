// ==============================================
// define a tiny Fp, p = 101
// ==============================================

use ark_ff::{BigInt, Field, Fp, Fp64, MontBackend, MontConfig, One, PrimeField, Zero};

const PRIME: u64 = 101;
pub struct FpConfig;

impl MontConfig<1> for FpConfig {
    const MODULUS: ark_ff::BigInt<1> = BigInt([PRIME]);
    const GENERATOR: ark_ff::Fp<ark_ff::MontBackend<Self, 1>, 1> = Fp64::new(BigInt([2u64]));
    const TWO_ADIC_ROOT_OF_UNITY: ark_ff::Fp<ark_ff::MontBackend<Self, 1>, 1> =
        Fp64::new(BigInt([1u64]));
}

pub type TinyFp = Fp64<MontBackend<FpConfig, 1>>;

// ==============================================
// Extension field Fp^2 = Fp[i] / (i^2 + 1)
// ==============================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Fp2 {
    c0: TinyFp, // real part
    c1: TinyFp, // imaginary part
}

impl Fp2 {
    fn new(c0: TinyFp, c1: TinyFp) -> Self {
        Fp2 { c0, c1 }
    }

    fn zero() -> Self {
        Fp2::new(TinyFp::ZERO, TinyFp::ZERO)
    }

    fn one() -> Self {
        Fp2::new(TinyFp::ONE, TinyFp::ONE)
    }

    fn add(&self, other: &Fp2) -> Fp2 {
        Fp2::new(self.c0 + other.c0, self.c1 + other.c1)
    }

    fn sub(&self, other: &Fp2) -> Fp2 {
        Fp2::new(self.c0 - other.c0, self.c1 - other.c1)
    }

    //  (a + bi)(c+di) = (ac-bd) + (ad+bc)i (i^2 = -1)
    fn mul(&self, other: &Fp2) -> Fp2 {
        let ac = self.c0 * other.c0;
        let bd = self.c1 * other.c1;
        // in fp: (a + b)(c+d) = ac + bd + (ad + bc)
        let ad_plus_bc = (self.c0 + self.c1) * (other.c0 + other.c1) - ac - bd;
        Fp2::new(ac - bd, ad_plus_bc)
    }

    fn scala_mul(&self, scala: TinyFp) -> Fp2 {
        Fp2::new(self.c0 * scala, self.c1 * scala)
    }

    fn square(&self) -> Fp2 {
        self.mul(self)
    }

    // conj( a+ bi) = a - bi
    fn conjugate(&self) -> Fp2 {
        Fp2::new(self.c0, -self.c1)
    }

    fn inverse(&self) -> Option<Fp2> {
        // (a + bi)^-1 = (a - bi) / (a^2 + b^2)
        let norm = self.c0 * self.c0 + self.c1 * self.c1;
        if norm == TinyFp::ZERO {
            return None;
        }
        let norm_inv = norm.inverse()?;
        Some(self.conjugate().scala_mul(norm_inv))
    }

    fn neg(&self) -> Fp2 {
        Fp2::new(-self.c0, -self.c1)
    }
}

// ==============================================
// define Elliptic Curve (affine Coordinates)
// ==============================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum G1Point {
    Infinity,
    Affine { x: TinyFp, y: TinyFp },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum G2Point {
    Infinity,
    Affine { x: Fp2, y: Fp2 },
}

impl G1Point {
    // Elliptic curve: E: y^2 = x^3 + 3 over TinyFp
    const B: u64 = 3;
    fn is_on_curve(&self) -> bool {
        match self {
            G1Point::Affine { x, y } => {
                let lhs = y * y;
                let rhs = x * x * x + TinyFp::from(G1Point::B);
                lhs == rhs
            }
            G1Point::Infinity => true,
        }
    }
    fn generator() -> Self {
        let point = G1Point::Affine {
            x: TinyFp::from(1u64),
            y: TinyFp::from(2u64),
        };
        debug_assert!(point.is_on_curve());
        point
    }

    fn add(&self, other: &G1Point) -> G1Point {
        match (self, other) {
            (G1Point::Infinity, _) => other.clone(),
            (_, G1Point::Infinity) => self.clone(),
            (G1Point::Affine { x: x1, y: y1 }, G1Point::Affine { x: x2, y: y2 }) => {
                if x1 == x2 {
                    if y1 == y2 {
                        return self.double();
                    } else {
                        return G1Point::Infinity;
                    }
                }

                // standard point addition
                let lambda = (*y2 - *y1) * (*x2 - *x1).inverse().unwrap();
                let x3 = lambda * lambda - *x1 - *x2;
                let y3 = lambda * (*x1 - x3) - *y1;
                G1Point::Affine { x: x3, y: y3 }
            }
        }
    }

    /// point double
    fn double(&self) -> G1Point {
        match self {
            G1Point::Infinity => G1Point::Infinity,
            G1Point::Affine { x, y } => {
                if *y == TinyFp::ZERO {
                    return G1Point::Infinity;
                }
                let three = TinyFp::from(3u64);
                let two = TinyFp::from(2u64);
                let lambda = three * (*x) * (*x) * (two * *y).inverse().unwrap();
                let x3 = lambda * lambda - two * *x;
                let y3 = lambda * (*x - x3) - *y;
                G1Point::Affine { x: x3, y: y3 }
            }
        }
    }

    // Point negative -(x, y) = (x, -y)
    fn negate(&self) -> G1Point {
        match self {
            G1Point::Infinity => G1Point::Infinity,
            G1Point::Affine { x, y } => G1Point::Affine { x: *x, y: -*y },
        }
    }

    fn sub(&self, other: &G1Point) -> G1Point {
        self.add(&other.negate())
    }
}

impl G2Point {
    // Elliptic curve: E: y^2 = x^3 + 3 over Fp2
    const B: u64 = 3;
    fn is_on_curve(&self) -> bool {
        match self {
            G2Point::Infinity => true,
            G2Point::Affine { x, y } => {
                let lhs = y.square();
                let three = Fp2::new(TinyFp::from(Self::B), TinyFp::ZERO);
                let rhs = x.square().mul(x).add(&three);
                lhs == rhs
            }
        }
    }
    fn generator() -> Self {
        // (0 + 3i, 9 + 49i)
        // Verified: (9 + 49i)^2 = (3i)^3 + 3 = 3 + 74i (mod 101)
        let point = G2Point::Affine {
            x: Fp2::new(TinyFp::from(0u64), TinyFp::from(3u64)),
            y: Fp2::new(TinyFp::from(9u64), TinyFp::from(49u64)),
        };
        debug_assert!(point.is_on_curve());
        point
    }

    fn add(&self, other: &G2Point) -> G2Point {
        match (self, other) {
            (G2Point::Infinity, _) => other.clone(),
            (_, G2Point::Infinity) => self.clone(),
            (G2Point::Affine { x: x1, y: y1 }, G2Point::Affine { x: x2, y: y2 }) => {
                if x1 == x2 {
                    if y1 == y2 {
                        return self.double();
                    } else {
                        return G2Point::Infinity;
                    }
                }

                // standard point addition
                let dy = y2.sub(y1);
                let dx_inv = x2.sub(x1).inverse().unwrap();
                let lambda = dy.mul(&dx_inv);
                let x3 = lambda.square().sub(x1).sub(x2);
                let y3 = lambda.mul(&x1.sub(&x3)).sub(y1);
                G2Point::Affine { x: x3, y: y3 }
            }
        }
    }

    /// point double
    fn double(&self) -> G2Point {
        match self {
            G2Point::Infinity => G2Point::Infinity,
            G2Point::Affine { x, y } => {
                if *y == Fp2::zero() {
                    return G2Point::Infinity;
                }
                let three = Fp2::new(TinyFp::from(3u64), TinyFp::ZERO);
                let two = Fp2::new(TinyFp::from(2u64), TinyFp::ZERO);
                let numerator = three.mul(&x.square());
                let demoninator = two.mul(y);
                let lambda = numerator.mul(&demoninator.inverse().unwrap());
                let x3 = lambda.square().sub(&two.mul(x));
                let y3 = lambda.mul(&x.sub(&x3)).sub(y);
                G2Point::Affine { x: x3, y: y3 }
            }
        }
    }

    fn scala_mul(&self, scala: TinyFp) -> G2Point {
        let mut result = G2Point::Infinity;
        let mut temp = self.clone();
        let scala_bits = scala.into_bigint().0[0];
        for i in 0..64 {
            if (scala_bits >> i) & 1 == 1 {
                result = result.add(&temp)
            }
            temp = temp.double()
        }

        result
    }

    // Point negative -(x, y) = (x, -y)
    fn negate(&self) -> G2Point {
        match self {
            G2Point::Infinity => G2Point::Infinity,
            G2Point::Affine { x, y } => G2Point::Affine { x: *x, y: y.neg() },
        }
    }

    fn sub(&self, other: &G2Point) -> G2Point {
        self.add(&other.negate())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fp(v: u64) -> TinyFp {
        TinyFp::from(v)
    }

    fn fp2(a: u64, b: u64) -> Fp2 {
        Fp2::new(fp(a), fp(b))
    }

    #[test]
    fn test_fp_works() {
        let a = TinyFp::from(100u64);
        let b = TinyFp::from(2u64);
        assert_eq!(a + b, TinyFp::from(102 % PRIME));

        let a = TinyFp::from(100u64);
        let b = TinyFp::from(2u64);
        assert_eq!(a - b, TinyFp::from(98 % PRIME));

        let a = TinyFp::from(100u64);
        let b = TinyFp::from(2u64);
        assert_eq!(b - a, TinyFp::from((2 - 100 + PRIME as i64) as u64));

        let a = TinyFp::from(100u64);
        let b = TinyFp::from(2u64);
        assert_eq!(a * b, TinyFp::from(200 % PRIME));

        let a = TinyFp::from(60u64);
        let b = TinyFp::from(2u64);
        assert_eq!(a / b, TinyFp::from(30 % PRIME));
    }

    #[test]
    fn test_g1_add_double_expected() {
        let g = G1Point::generator();
        let g2 = g.add(&g);
        assert_eq!(
            g2,
            G1Point::Affine {
                x: fp(68),
                y: fp(74)
            }
        );

        let g3 = g2.add(&g);
        assert_eq!(
            g3,
            G1Point::Affine {
                x: fp(26),
                y: fp(45)
            }
        );

        assert_eq!(g.double(), g2);
    }

    #[test]
    fn test_g1_negate_sub_identity() {
        let g = G1Point::generator();
        assert_eq!(g.add(&G1Point::Infinity), g);
        assert_eq!(G1Point::Infinity.add(&g), g);
        assert_eq!(g.add(&g.negate()), G1Point::Infinity);
        assert_eq!(g.sub(&g), G1Point::Infinity);
    }

    #[test]
    fn test_g1_double_y_zero_is_infinity() {
        let p = G1Point::Affine {
            x: fp(48),
            y: fp(0),
        };
        assert_eq!(p.double(), G1Point::Infinity);
    }

    #[test]
    fn test_g2_generator_on_curve() {
        let g = G2Point::generator();
        assert!(g.is_on_curve());
    }

    #[test]
    fn test_g2_add_double_expected() {
        let g = G2Point::generator();
        let g2 = g.add(&g);
        assert_eq!(
            g2,
            G2Point::Affine {
                x: fp2(38, 33),
                y: fp2(61, 75)
            }
        );

        let g3 = g2.add(&g);
        assert_eq!(
            g3,
            G2Point::Affine {
                x: fp2(19, 91),
                y: fp2(88, 44)
            }
        );

        assert_eq!(g.double(), g2);
    }

    #[test]
    fn test_g2_negate_sub_identity() {
        let g = G2Point::generator();
        assert_eq!(g.add(&G2Point::Infinity), g);
        assert_eq!(G2Point::Infinity.add(&g), g);
        assert_eq!(g.add(&g.negate()), G2Point::Infinity);
        assert_eq!(g.sub(&g), G2Point::Infinity);
    }

    #[test]
    fn test_g2_scalar_mul_matches_add() {
        let g = G2Point::generator();
        let g2 = g.add(&g);
        let g3 = g2.add(&g);
        assert_eq!(g.scala_mul(fp(2)), g2);
        assert_eq!(g.scala_mul(fp(3)), g3);
    }
}
