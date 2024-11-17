/*++ @file

  Copyright ©2021-2024 Liu Yi, efikarl@yeah.net

  This program is just made available under the terms and conditions of the
  MIT license: http://www.efikarl.com/mit-license.html

  THE PROGRAM IS DISTRIBUTED UNDER THE MIT LICENSE ON AN "AS IS" BASIS,
  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.
--*/

use num_traits::{Zero,One};
use num_bigint::{BigUint,RandBigInt,BigInt,Sign};

trait Prime<T> {
    fn random_prime(bits: u64) -> T;
    fn is_prime(&self) -> bool;
    fn prime_test_of_fermat(&self) -> bool;
    fn prime_test_of_miller(&self) -> bool;
}

impl Prime<BigUint> for BigUint {
    fn random_prime(bits: u64) -> BigUint {
        let mut rng = rand::thread_rng();
        let lbound  = BigUint::one() << ((bits >> 1) - 1);
        let ubound  = BigUint::one() << ((bits >> 1) + 1);
        loop {
            let n: BigUint = rng.gen_biguint_range(&lbound, &ubound);
            if n.is_prime() == true {
                return n;
            }
        }
    }

    fn is_prime(&self) -> bool {
        if self.bit(0) == false {
            return false;
        }

        if !self.prime_test_of_fermat() {
            return false;
        }

        if !self.prime_test_of_miller() {
            return false;
        }

        return true;
    }

    fn prime_test_of_fermat(&self) -> bool {
        let ref x1 = BigUint::one();

        let mut b = x1 + x1;
        let ref n_minus_1 = self - x1;
        loop {
            if b >= BigUint::from_slice(&[8]) || &b > self {
                break;
            }
            let ref result = b.modpow(&n_minus_1, self);
            if result != x1 {
                return false;
            }

            b = b + x1;
        }

        return true;
    }

    fn prime_test_of_miller(&self) -> bool {
        let ref x0 = BigUint::zero();
        let ref x1 = BigUint::one();
        let ref x2 = x1 + x1;

        if self % x2 == *x0 {
            return false;
        }
        // Miller-Rabin's Test
        let mut b = x1 + x1;
        let mut n_minus_1 = self - x1;

        loop {
            if b >= BigUint::from_slice(&[4]) {
                break;
            }
            if b >= n_minus_1 {
                break;
            }

            let mut x = b.clone();
            let mut r = BigUint::one();
            while &n_minus_1 != x0 {
                if n_minus_1.bit(0) {
                    r = &r * &x % self;
                };

                let s = x.clone();
                x = &x * &x % self;
                if &x == x1 && !(s == *x1 || s == n_minus_1) {
                    return false;
                };
                n_minus_1 = &n_minus_1 >> 1;
            }
            if !r.is_one() {
                return false;
            }

            b = b + x1;
        }

        return true;
    }
}

#[derive(Clone, Debug)]
struct Key {
    p       : BigUint,
    q       : BigUint,
    n       : BigUint,
    e       : BigUint,
    d       : BigUint,
}

#[derive(Clone, Debug)]
pub struct Rsa {
    inner   : Key,
}

impl Rsa {
    pub fn new(bits: u64) -> Self {
        let mut k;
        loop {
            k = Rsa::init(bits);
            if k.check() {
                break;
            }
        }

        k
    }

    pub fn ek(&self) -> (BigUint, BigUint) {
        (self.inner.n.clone(), self.inner.e.clone())
    }

    pub fn dk(&self) -> (BigUint, BigUint) {
        (self.inner.n.clone(), self.inner.d.clone())
    }

    fn init(bits: u64) -> Self {
        let x1 = BigUint::one();

        let mut p;
        let mut q;
        let mut n;
        loop {
            p = BigUint::random_prime(bits);
            q = BigUint::random_prime(bits);
            if p == q {
                continue
            }
            n = &p * &q;
            if bits == n.bits() {
                break;
            }
        }
        // :l is \lambda(n) in (pkcs) #1
        let l = (&p - &x1) * (&q - &x1);
        let mut e;
        let mut d;
        loop {
            e = Self::calculate_e(&l, &n);
            d = Self::calculate_d(&l, &n, &e);
            if &e * &d % &l == x1 {
                break;
            }
        }

        Self { inner: Key { p, q, n, e, d } }
    }

    fn ep(&self, m: &BigUint) -> BigUint {
        let c = m.modpow(&self.inner.e, &self.inner.n);
        c
    }

    fn dp(&self, c: &BigUint) -> BigUint {
        let m = c.modpow(&self.inner.d, &self.inner.n);
        m
    }

    fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
        let max;
        let min;
        if a > b {
            max = a;
            min = b;
        } else {
            max = b;
            min = a;
        }
        if min.is_zero() {
            return max.clone();
        }

        Self::gcd(min, &(max % min))
    }

    fn gcd_ex(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
        let mut q;
        let mut d;
        let mut r;
        if a > b {
            d = a.clone(); r = b.clone();
        } else {
            d = b.clone(); r = a.clone();
        }
        let mut u = BigInt::one();
        let mut v = BigInt::zero();
        let mut s = BigInt::zero();
        let mut t = BigInt::one();

        while !r.is_zero() {
            // q, r = divmod(d, r)
            let p = r.clone(); q = &d / &r; r = &d % &r; d = p;
            // gcd(a, b) = ax + by
            let p = u; u = s.clone(); s = p - &q * &s;
            let p = v; v = t.clone(); t = p - &q * &t;
        }

        if a > b {
            return (d, u, v);
        } else {
            return (d, v, u);
        }
    }

    fn calculate_e(l: &BigUint, n: &BigUint) -> BigUint {
        let mut rng = rand::thread_rng();
        loop {
            let u = rng.gen_biguint_range(&BigUint::one(), n);
            if Self::gcd(l, &u).is_one() {
                return u;
            }
        }
    }

    fn calculate_d(l: &BigUint, n: &BigUint, e: &BigUint) -> BigUint {
        let (_, _, d) = Self::gcd_ex (
            &BigInt::from_slice(Sign::Plus, l.to_u32_digits().as_slice()),
            &BigInt::from_slice(Sign::Plus, e.to_u32_digits().as_slice()),
        );

        let n_as_int = BigInt::from_slice(Sign::Plus, n.to_u32_digits().as_slice());
        let d = &d % &n_as_int;
        let d = if d < BigInt::zero() { d + n_as_int } else { d };

        d.to_biguint().unwrap()
    }

    fn check(&self) -> bool {
        let x1 = BigUint::one();

        let l = (&self.inner.p - &x1) * (&self.inner.q - &x1);
        if &self.inner.e * &self.inner.d % &l != x1 {
            return false;
        }
        let mut i_m = BigUint::zero();
        loop {
            if i_m > BigUint::from(8u8) {
                break;
            }
            let o_c = self.ep(&i_m);
            let o_m = self.dp(&o_c);
            if i_m != o_m {
                return false;
            }

            i_m += BigUint::one();
        }
        return true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rsa_ep_dp_test() {
        let rsa = Rsa::new(8);
        println!("{:#?}", rsa);

        let mut i_m = BigUint::zero();
        loop {
            if &i_m >= &rsa.inner.n {
                break;
            }
            let o_c = rsa.ep(&i_m);
            let o_m = rsa.dp(&o_c);
            assert_eq!(i_m, o_m);

            println!("i_m = {}", i_m);
            println!("o_c = {}", o_c);
            println!("o_m = {}", o_m);

            i_m += BigUint::one();
        }
    }

    #[test]
    fn rsa_test_n() {
        let rsa = Rsa::new(8);
        println!("{:#?}", rsa);

        let ref n = &rsa.inner.p * &rsa.inner.q;
        assert_eq!(&rsa.inner.n, n);
    }

    #[test]
    fn rsa_test_e_1() {
        let rsa = Rsa::new(8);
        println!("{:#?}", rsa);

        assert!(rsa.inner.e < &rsa.inner.p * &rsa.inner.q);
    }

    #[test]
    fn rsa_test_e_2() {
        let rsa = Rsa::new(8);
        println!("{:#?}", rsa);

        let ref l = (&rsa.inner.p - BigUint::one()) * (&rsa.inner.q - BigUint::one());
        assert_eq!(BigUint::one(), Rsa::gcd(&rsa.inner.e, l));
    }

    #[test]
    fn rsa_test_d() {
        let rsa = Rsa::new(8);
        println!("{:#?}", rsa);

        let ref l = (&rsa.inner.p - BigUint::one()) * (&rsa.inner.q - BigUint::one());
        assert_eq!(BigUint::one(), &rsa.inner.e * &rsa.inner.d % l);
    }

    #[test]
    fn rsa_prime_test() {
        let rsa = Rsa::new(512);
        println!("{:#?}", rsa);
    }
}
