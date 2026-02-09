use ark_ff::Field;

use crate::tiny_field::{Fp2, G1Point, G2Point, PRIME, TinyFp};

// order of G1 and G2 group
const R: u64 = 17;

// Toy target group in the smallest extension field that contains Fp2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GT(Fp2);

impl GT {
    pub fn new(inner: Fp2) -> Self {
        GT(inner)
    }

    pub fn one() -> Self {
        GT(Fp2::one())
    }

    pub fn mul(&self, other: &GT) -> GT {
        GT(self.0.mul(&other.0))
    }

    pub fn pow(&self, mut exp: u64) -> GT {
        let mut acc = GT::one();
        let mut cur = *self;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc.mul(&cur);
            }
            cur = cur.mul(&cur);
            exp >>= 1;
        }
        acc
    }
}

fn line_eval(r: &G1Point, s: &G1Point, q: &G2Point) -> (Fp2, G1Point) {
    let (x1, y1) = match r {
        G1Point::Affine { x, y } => (*x, *y),
        G1Point::Infinity => panic!("R must be affine in line evaluation"),
    };
    let (x2, y2) = match s {
        G1Point::Affine { x, y } => (*x, *y),
        G1Point::Infinity => panic!("S must be affine in line evaluation"),
    };
    let (xq, yq) = match q {
        G2Point::Affine { x, y } => (*x, *y),
        G2Point::Infinity => panic!("Q must be affine in line evaluation"),
    };

    let x1_fp2 = Fp2::from(x1);
    let y1_fp2 = Fp2::from(y1);
    let xq_minus_x1 = xq.sub(&x1_fp2);
    let yq_minus_y1 = yq.sub(&y1_fp2);

    if x1 == x2 && y1 + y2 == TinyFp::ZERO {
        let g = xq.sub(&Fp2::from(x1));
        return (g, G1Point::Infinity);
    }

    let (lambda, x3, y3) = if x1 == x2 && y1 == y2 {
        if y1 == TinyFp::ZERO {
            let g = xq.sub(&Fp2::from(x1));
            return (g, G1Point::Infinity);
        }
        let three = TinyFp::from(3u64);
        let two = TinyFp::from(2u64);
        let num = three * x1 * x1;
        let den = (two * y1).inverse().unwrap();
        let lam = num * den;
        let x3 = lam * lam - two * x1;
        let y3 = lam * (x1 - x3) - y1;
        (lam, x3, y3)
    } else {
        let lam = (y2 - y1) * (x2 - x1).inverse().unwrap();
        let x3 = lam * lam - x1 - x2;
        let y3 = lam * (x1 - x3) - y1;
        (lam, x3, y3)
    };

    let lam_fp2 = Fp2::from(lambda);
    let line = yq_minus_y1.sub(&lam_fp2.mul(&xq_minus_x1));
    let v = xq.sub(&Fp2::from(x3));
    let g = line.mul(&v.inverse().unwrap());
    (g, G1Point::Affine { x: x3, y: y3 })
}

fn miller_loop(p: &G1Point, q: &G2Point) -> Fp2 {
    let mut f = Fp2::one();
    let mut r = *p;

    let mut bits = Vec::new();
    let mut n = R;
    while n > 0 {
        bits.push((n & 1) as u8);
        n >>= 1;
    }

    for i in (0..bits.len() - 1).rev() {
        let (g, r2) = line_eval(&r, &r, q);
        f = f.square().mul(&g);
        r = r2;
        if bits[i] == 1 {
            let (g2, r3) = line_eval(&r, p, q);
            f = f.mul(&g2);
            r = r3;
        }
    }

    f
}

// Reduced Tate pairing on a supersingular toy curve.
// This is only for educational use and is NOT cryptographically secure.
pub fn pairing(p: &G1Point, q: &G2Point) -> GT {
    match (p, q) {
        (G1Point::Infinity, _) | (_, G2Point::Infinity) => GT::one(),
        _ => {
            let f = miller_loop(p, q);
            let p = PRIME as u128;
            let exp = ((p * p - 1) / (R as u128)) as u64;
            GT::new(f).pow(exp)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pairing_bilinear_property() {
        // e(aP, bQ) = e(P, Q)^(ab)
        let g1 = G1Point::generator();
        let g2 = G2Point::generator();
        let a = 2u64;
        let b = 3u64;

        let p = g1.scalar_mul(a);
        let q = g2.scala_mul(TinyFp::from(b));

        let left = pairing(&p, &q);
        let right = pairing(&g1, &g2).pow(a * b);

        assert_eq!(left, right);
    }

    #[test]
    fn test_pairing_multiple_cases() {
        let g1 = G1Point::generator();
        let g2 = G2Point::generator();

        for a in 0u64..5 {
            for b in 0u64..5 {
                // e(aP, bQ) = e(P, Q)^(ab)
                let p = g1.scalar_mul(a);
                let q = g2.scala_mul(TinyFp::from(b));
                let left = pairing(&p, &q);
                let right = pairing(&g1, &g2).pow(a * b);
                assert_eq!(left, right, "a={a}, b={b}");
            }
        }
    }

    #[test]
    fn test_pairing_bilinear_in_each_argument() {
        // e(P1+P2, Q) = e(P1, Q) * e(P2, Q)
        // e(P, Q1+Q2) = e(P, Q1) * e(P, Q2)
        let g1 = G1Point::generator();
        let g2 = G2Point::generator();

        let p1 = g1.scalar_mul(2);
        let p2 = g1.scalar_mul(5);
        let q1 = g2.scala_mul(TinyFp::from(3u64));
        let q2 = g2.scala_mul(TinyFp::from(4u64));

        let left_p = pairing(&p1.add(&p2), &q1);
        let right_p = pairing(&p1, &q1).mul(&pairing(&p2, &q1));
        assert_eq!(left_p, right_p);

        let left_q = pairing(&p1, &q1.add(&q2));
        let right_q = pairing(&p1, &q1).mul(&pairing(&p1, &q2));
        assert_eq!(left_q, right_q);
    }

    #[test]
    fn test_pairing_with_infinity() {
        // e(O, Q) = 1 and e(P, O) = 1
        let g1 = G1Point::generator();
        let g2 = G2Point::generator();

        let e1 = pairing(&G1Point::Infinity, &g2);
        let e2 = pairing(&g1, &G2Point::Infinity);
        assert_eq!(e1, GT::one());
        assert_eq!(e2, GT::one());
    }
}
