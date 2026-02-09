// ==============================================
// define a tiny Fp, p = 101
// ==============================================

use ark_ff::{BigInt, Field, Fp64, MontBackend, MontConfig, PrimeField};

pub const BASE_FIELD_MODULUS: u64 = 101;
pub const SCALAR_FIELD_MODULUS: u64 = 17;
pub struct FpConfig;
pub struct FrConfig;

impl MontConfig<1> for FpConfig {
    const MODULUS: ark_ff::BigInt<1> = BigInt([BASE_FIELD_MODULUS]);
    const GENERATOR: ark_ff::Fp<ark_ff::MontBackend<Self, 1>, 1> = Fp64::new(BigInt([2u64]));
    const TWO_ADIC_ROOT_OF_UNITY: ark_ff::Fp<ark_ff::MontBackend<Self, 1>, 1> =
        Fp64::new(BigInt([1u64]));
}

pub type BaseField = Fp64<MontBackend<FpConfig, 1>>;

impl MontConfig<1> for FrConfig {
    const MODULUS: ark_ff::BigInt<1> = BigInt([SCALAR_FIELD_MODULUS]);
    const GENERATOR: ark_ff::Fp<ark_ff::MontBackend<Self, 1>, 1> = Fp64::new(BigInt([3u64]));
    const TWO_ADIC_ROOT_OF_UNITY: ark_ff::Fp<ark_ff::MontBackend<Self, 1>, 1> =
        Fp64::new(BigInt([1u64]));
}

pub type ScalarField = Fp64<MontBackend<FrConfig, 1>>;

// ==============================================
// Extension field Fp^2 = Fp[i] / (i^2 - NON_RESIDUE)
// ==============================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fp2 {
    c0: BaseField, // real part
    c1: BaseField, // imaginary part
}

impl Fp2 {
    const NON_RESIDUE: u64 = 2;
    pub fn new(c0: BaseField, c1: BaseField) -> Self {
        Fp2 { c0, c1 }
    }

    pub fn zero() -> Self {
        Fp2::new(BaseField::ZERO, BaseField::ZERO)
    }

    pub fn one() -> Self {
        Fp2::new(BaseField::ONE, BaseField::ZERO)
    }

    pub fn add(&self, other: &Fp2) -> Fp2 {
        Fp2::new(self.c0 + other.c0, self.c1 + other.c1)
    }

    pub fn sub(&self, other: &Fp2) -> Fp2 {
        Fp2::new(self.c0 - other.c0, self.c1 - other.c1)
    }

    //  (a + bi)(c+di) = (ac + bd * nr) + (ad + bc)i (i^2 = nr)
    pub fn mul(&self, other: &Fp2) -> Fp2 {
        let ac = self.c0 * other.c0;
        let bd = self.c1 * other.c1;
        let nr = BaseField::from(Self::NON_RESIDUE);
        let ad_plus_bc = self.c0 * other.c1 + self.c1 * other.c0;
        Fp2::new(ac + bd * nr, ad_plus_bc)
    }

    pub fn scala_mul(&self, scala: BaseField) -> Fp2 {
        Fp2::new(self.c0 * scala, self.c1 * scala)
    }

    pub fn square(&self) -> Fp2 {
        self.mul(self)
    }

    // conj( a+ bi) = a - bi
    pub fn conjugate(&self) -> Fp2 {
        Fp2::new(self.c0, -self.c1)
    }

    pub fn inverse(&self) -> Option<Fp2> {
        // (a + bi)^-1 = (a - bi) / (a^2 - nr * b^2)
        let nr = BaseField::from(Self::NON_RESIDUE);
        let norm = self.c0 * self.c0 - nr * self.c1 * self.c1;
        if norm == BaseField::ZERO {
            return None;
        }
        let norm_inv = norm.inverse()?;
        Some(self.conjugate().scala_mul(norm_inv))
    }

    pub fn neg(&self) -> Fp2 {
        Fp2::new(-self.c0, -self.c1)
    }
}

impl From<BaseField> for Fp2 {
    fn from(value: BaseField) -> Self {
        Fp2::new(value, BaseField::from(0u64))
    }
}

// ==============================================
// define Elliptic Curve (affine Coordinates)
// ==============================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum G1Point {
    Infinity,
    Affine { x: BaseField, y: BaseField },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum G2Point {
    Infinity,
    Affine { x: Fp2, y: Fp2 },
}

impl G1Point {
    // Elliptic curve: E: y^2 = x^3 + 3 over BaseField Fp
    const B: u64 = 3;
    pub fn is_on_curve(&self) -> bool {
        match self {
            G1Point::Affine { x, y } => {
                let lhs = y * y;
                let rhs = x * x * x + BaseField::from(G1Point::B);
                lhs == rhs
            }
            G1Point::Infinity => true,
        }
    }
    pub fn generator() -> Self {
        let point = G1Point::Affine {
            x: BaseField::from(1u64),
            y: BaseField::from(2u64),
        };
        debug_assert!(point.is_on_curve());
        point
    }

    pub fn add(&self, other: &G1Point) -> G1Point {
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
    pub fn double(&self) -> G1Point {
        match self {
            G1Point::Infinity => G1Point::Infinity,
            G1Point::Affine { x, y } => {
                if *y == BaseField::ZERO {
                    return G1Point::Infinity;
                }
                let three = BaseField::from(3u64);
                let two = BaseField::from(2u64);
                let lambda = three * (*x) * (*x) * (two * *y).inverse().unwrap();
                let x3 = lambda * lambda - two * *x;
                let y3 = lambda * (*x - x3) - *y;
                G1Point::Affine { x: x3, y: y3 }
            }
        }
    }

    // Point negative -(x, y) = (x, -y)
    pub fn negate(&self) -> G1Point {
        match self {
            G1Point::Infinity => G1Point::Infinity,
            G1Point::Affine { x, y } => G1Point::Affine { x: *x, y: -*y },
        }
    }

    pub fn sub(&self, other: &G1Point) -> G1Point {
        self.add(&other.negate())
    }

    pub fn scalar_mul_u64(&self, mut k: u64) -> G1Point {
        let mut acc = G1Point::Infinity;
        let mut cur = *self;
        while k > 0 {
            if k & 1 == 1 {
                acc = acc.add(&cur);
            }
            cur = cur.double();
            k >>= 1;
        }
        acc
    }

    pub fn scalar_mul_fr(&self, k: ScalarField) -> G1Point {
        let bits = k.into_bigint().0[0];
        self.scalar_mul_u64(bits)
    }
}

impl G2Point {
    // Elliptic curve: E: y^2 = x^3 + 3 over Fp2
    const B: u64 = 3;
    pub fn is_on_curve(&self) -> bool {
        match self {
            G2Point::Infinity => true,
            G2Point::Affine { x, y } => {
                let lhs = y.square();
                let three = Fp2::new(BaseField::from(Self::B), BaseField::ZERO);
                let rhs = x.square().mul(x).add(&three);
                lhs == rhs
            }
        }
    }
    pub fn generator() -> Self {
        // Distortion map of G1 generator: (x, y) -> (xi * x, y),
        // where xi^2 + xi + 1 = 0 in Fp2.
        let point = G2Point::Affine {
            x: Fp2::new(BaseField::from(50u64), BaseField::from(47u64)),
            y: Fp2::new(BaseField::from(2u64), BaseField::from(0u64)),
        };
        debug_assert!(point.is_on_curve());
        point
    }

    pub fn add(&self, other: &G2Point) -> G2Point {
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
    pub fn double(&self) -> G2Point {
        match self {
            G2Point::Infinity => G2Point::Infinity,
            G2Point::Affine { x, y } => {
                if *y == Fp2::zero() {
                    return G2Point::Infinity;
                }
                let three = Fp2::new(BaseField::from(3u64), BaseField::ZERO);
                let two = Fp2::new(BaseField::from(2u64), BaseField::ZERO);
                let numerator = three.mul(&x.square());
                let demoninator = two.mul(y);
                let lambda = numerator.mul(&demoninator.inverse().unwrap());
                let x3 = lambda.square().sub(&two.mul(x));
                let y3 = lambda.mul(&x.sub(&x3)).sub(y);
                G2Point::Affine { x: x3, y: y3 }
            }
        }
    }

    pub fn scalar_mul_u64(&self, mut k: u64) -> G2Point {
        let mut acc = G2Point::Infinity;
        let mut cur = *self;
        while k > 0 {
            if k & 1 == 1 {
                acc = acc.add(&cur);
            }
            cur = cur.double();
            k >>= 1;
        }
        acc
    }

    pub fn scalar_mul_fr(&self, k: ScalarField) -> G2Point {
        let bits = k.into_bigint().0[0];
        self.scalar_mul_u64(bits)
    }

    // Point negative -(x, y) = (x, -y)
    pub fn negate(&self) -> G2Point {
        match self {
            G2Point::Infinity => G2Point::Infinity,
            G2Point::Affine { x, y } => G2Point::Affine { x: *x, y: y.neg() },
        }
    }

    pub fn sub(&self, other: &G2Point) -> G2Point {
        self.add(&other.negate())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fp(v: u64) -> BaseField {
        BaseField::from(v)
    }

    fn fp2(a: u64, b: u64) -> Fp2 {
        Fp2::new(fp(a), fp(b))
    }

    #[test]
    fn test_fp_works_success() {
        let a = BaseField::from(100u64);
        let b = BaseField::from(2u64);
        assert_eq!(a + b, BaseField::from(102 % BASE_FIELD_MODULUS));

        let a = BaseField::from(100u64);
        let b = BaseField::from(2u64);
        assert_eq!(a - b, BaseField::from(98 % BASE_FIELD_MODULUS));

        let a = BaseField::from(100u64);
        let b = BaseField::from(2u64);
        assert_eq!(
            b - a,
            BaseField::from((2 - 100 + BASE_FIELD_MODULUS as i64) as u64)
        );

        let a = BaseField::from(100u64);
        let b = BaseField::from(2u64);
        assert_eq!(a * b, BaseField::from(200 % BASE_FIELD_MODULUS));

        let a = BaseField::from(60u64);
        let b = BaseField::from(2u64);
        assert_eq!(a / b, BaseField::from(30 % BASE_FIELD_MODULUS));
    }

    #[test]
    fn test_g1_add_double_expected_success() {
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
    fn test_g1_negate_sub_identity_success() {
        let g = G1Point::generator();
        assert_eq!(g.add(&G1Point::Infinity), g);
        assert_eq!(G1Point::Infinity.add(&g), g);
        assert_eq!(g.add(&g.negate()), G1Point::Infinity);
        assert_eq!(g.sub(&g), G1Point::Infinity);
    }

    #[test]
    fn test_g1_double_y_zero_is_infinity_success() {
        let p = G1Point::Affine {
            x: fp(48),
            y: fp(0),
        };
        assert_eq!(p.double(), G1Point::Infinity);
    }

    #[test]
    fn test_g2_generator_on_curve_success() {
        let g = G2Point::generator();
        assert!(g.is_on_curve());
    }

    #[test]
    fn test_g2_add_double_expected_success() {
        let g = G2Point::generator();
        let g2 = g.add(&g);
        assert_eq!(
            g2,
            G2Point::Affine {
                x: fp2(67, 65),
                y: fp2(74, 0)
            }
        );

        let g3 = g2.add(&g);
        assert_eq!(
            g3,
            G2Point::Affine {
                x: fp2(88, 10),
                y: fp2(45, 0)
            }
        );

        assert_eq!(g.double(), g2);
    }

    #[test]
    fn test_g2_negate_sub_identity_success() {
        let g = G2Point::generator();
        assert_eq!(g.add(&G2Point::Infinity), g);
        assert_eq!(G2Point::Infinity.add(&g), g);
        assert_eq!(g.add(&g.negate()), G2Point::Infinity);
        assert_eq!(g.sub(&g), G2Point::Infinity);
    }

    #[test]
    fn test_g2_scalar_mul_matches_add_success() {
        let g = G2Point::generator();
        let g2 = g.add(&g);
        let g3 = g2.add(&g);
        assert_eq!(g.scalar_mul_u64(2), g2);
        assert_eq!(g.scalar_mul_u64(3), g3);
    }
}
