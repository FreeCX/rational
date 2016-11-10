//! Simple & tiny library for work with rational numbers
use std::ops::{Add, Sub, Mul, Div, Neg};
use std::cmp::{PartialEq, PartialOrd, Ordering};
use std::str::FromStr;
use std::num;
use std::fmt;

#[derive(Debug, Copy, Clone)]
pub struct Rational {
    numerator: i64,
    denominator: i64,
}

fn gcd(a: i64, b: i64) -> i64 {
    if a == 0 {
        b
    } else {
        gcd(b % a, a)
    }
}

fn lcm(a: i64, b: i64) -> i64 {
    (a * b).abs() / gcd(a, b)
}

impl Rational {
    /// Create `Rational` number
    ///
    /// # Example
    /// ```
    /// use rational::Rational;
    ///
    /// // initialize `a` by 10/2
    /// let a = Rational::new(10, 2);
    /// // you can use any integer types
    /// let b = Rational::new(5_u32, 25_i8);
    /// assert_eq!(a.value().ok(), Some(5.0));
    /// assert_eq!(b.value().ok(), Some(0.2));
    /// ```
    pub fn new<N, D>(numerator: N, denominator: D) -> Rational 
        where N: Into<i64>, D: Into<i64>
    {
        Rational {
            numerator: numerator.into(),
            denominator: denominator.into(),
        }
    }
    /// Create 1/1 `Rational` number
    ///
    /// # Example
    /// ```
    /// use rational::Rational;
    ///
    /// // init by 1/1
    /// let one = Rational::one();
    /// assert_eq!(one, Rational::new(1, 1));
    /// ```
    pub fn one() -> Rational {
        Rational::new(1, 1)
    }
    /// Return float value of `Rational` number
    ///
    /// # Example
    /// ```
    /// use rational::Rational;
    ///
    /// let a = Rational::new(3, 4);
    /// // get float value of `a`
    /// let r = a.value().ok();
    /// assert_eq!(r, Some(0.75));
    /// ```
    pub fn value(&self) -> Result<f64, String> {
        if self.denominator == 0 {
            // write enum for division by zero
            Err(format!("Division by zero: {:?}", self))
        } else {
            Ok(self.numerator as f64 / self.denominator as f64)
        }
    }
    /// Simplify `Rational` number
    ///
    /// # Example
    /// ```
    /// use rational::Rational;
    ///
    /// // create and simplify `Rational` number
    /// let a = Rational::new(10, 20).simplify();
    /// assert_eq!(a, Rational::new(1, 2));
    /// ```
    pub fn simplify(&mut self) -> Self {
        if self.numerator != 0 {
            let reducer = gcd(self.numerator.abs(), self.denominator.abs());
            self.numerator /= reducer;
            self.denominator /= reducer;
        }
        *self
    }
    /// Inverse `Rational` number
    ///
    /// # Example
    /// ```
    /// use rational::Rational;
    ///
    /// let a = Rational::new(1, 2);
    /// // b = a^(-1)
    /// let b = a.inverse();
    /// assert_eq!(b.value().unwrap(), 2.0);
    /// ```
    pub fn inverse(&self) -> Self {
        Rational::new(self.denominator, self.numerator)
    }
    /// Power `Rational` number to integer
    ///
    /// # Example
    /// ```
    /// use rational::Rational;
    ///
    /// // create 1/2 and power to 2
    /// let a = Rational::new(1, 2).pow(2);
    /// // create 1/2 and powet to -1
    /// let b = Rational::new(1, 2).pow(-1);
    /// assert_eq!(a, Rational::new(1, 4));
    /// assert_eq!(b, Rational::new(2, 1));
    /// ```
    pub fn pow(&self, n: i32) -> Self {
        let deg = n.abs() as u32;
        if n < 0 {
            Rational::new(
                self.denominator.pow(deg),
                self.numerator.pow(deg))
        } else if n == 0 {
            Rational::one()
        } else {
            Rational::new(
                self.numerator.pow(deg),
                self.denominator.pow(deg))
        }
    }
}

impl Add for Rational {
    type Output = Rational;

    fn add(self, _rhs: Self) -> Self {
        let lcm_v = lcm(self.denominator, _rhs.denominator);
        let mul_a = lcm_v / self.denominator;
        let mul_b = lcm_v / _rhs.denominator;
        Rational::new(mul_a * self.numerator + mul_b * _rhs.numerator, lcm_v)
    }
}

impl Neg for Rational {
    type Output = Rational;

    fn neg(self) -> Self {
        Rational::new(-self.numerator, self.denominator)
    }
}

impl Sub for Rational {
    type Output = Rational;

    fn sub(self, _rhs: Self) -> Self {
        self + (-_rhs)
    }
}

impl Mul for Rational {
    type Output = Rational;

    fn mul(self, _rhs: Self) -> Self {
        let a = self.numerator * _rhs.numerator;
        let b = self.denominator * _rhs.denominator;
        Rational::new(a, b)
    }
}

impl Div for Rational {
    type Output = Rational;

    fn div(self, _rhs: Self) -> Self {
        let n_rhs = _rhs.inverse();
        self * n_rhs
    }
}

impl<I: Into<i64>> Add<I> for Rational {
    type Output = Rational;

    fn add(self, _rhs: I) -> Self::Output {
        (self + Rational::new(_rhs.into(), 1))
    }
}

impl<I: Into<i64>> Sub<I> for Rational {
    type Output = Rational;

    fn sub(self, _rhs: I) -> Self::Output {
        (self - Rational::new(_rhs.into(), 1))
    }
}

impl<I: Into<i64>> Mul<I> for Rational {
    type Output = Rational;

    fn mul(self, _rhs: I) -> Self::Output {
        Rational::new(self.numerator * _rhs.into(), self.denominator)
    }
}

impl<I: Into<i64>> Div<I> for Rational {
    type Output = Rational;

    fn div(self, _rhs: I) -> Self::Output {
        Rational::new(self.numerator, self.denominator * _rhs.into())
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        self.numerator * other.denominator == self.denominator * other.numerator
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let first = self.numerator * other.denominator < self.denominator * other.numerator;
        let second = self.numerator * other.denominator > self.denominator * other.numerator;
        if first {
            Some(Ordering::Less)
        } else if second {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl FromStr for Rational {
    type Err = num::ParseIntError;
    
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let words: Vec<&str> = s.split('/').collect();
        let x: i64 = words[0].parse()?;
        let y: i64 = words[1].parse()?;
        Ok(Self::new(x, y))
    }
}

#[cfg(test)]
mod rational_test {
    use super::*;

    #[test]
    fn addition() {
        assert_eq!(Rational::new(3, 4) + Rational::new(5, 6), Rational::new(19, 12));
        assert_eq!(Rational::new(1, 2) + Rational::new(2, 4), Rational::new(1, 1));
        assert_eq!(Rational::new(0, 1) + Rational::new(2, 1), Rational::new(2, 1));
    }

    #[test]
    fn substraction() {
        assert_eq!(Rational::new(1, 2) - Rational::new(2, 2), Rational::new(-1, 2));
        assert_eq!(Rational::new(10, 2) - Rational::new(4, 1), Rational::new(1, 1));
        assert_eq!(Rational::new(3, 4) - Rational::new(-1, 4), Rational::new(1, 1));
    }

    #[test]
    fn multiplication() {
        assert_eq!(Rational::new(3, 4) * Rational::new(2, 2), Rational::new(3, 4));
        assert_eq!(Rational::new(1, 2) * Rational::new(0, 2), Rational::new(0, 4));
        assert_eq!(Rational::new(2, 1) * Rational::new(1, 2), Rational::new(1, 1));
    }

    #[test]
    fn division() {
        assert_eq!(Rational::new(1, 2) / Rational::new(2, 1), Rational::new(1, 4));
        assert_eq!(Rational::new(3, 4) / Rational::new(1, 2), Rational::new(3, 2));
        assert_eq!(Rational::new(0, 2) / Rational::new(1, 2), Rational::new(0, 2));
    }

    #[test]
    fn mul_to_const() {
        assert_eq!(Rational::new(10, 3) * 4_u8, Rational::new(40, 3));
        assert_eq!(Rational::new(4, 3) * 5_i32, Rational::new(20, 3));
        assert_eq!(Rational::new(1, 5) * 6, Rational::new(6, 5));
    }

    #[test]
    fn div_to_const() {
        assert_eq!(Rational::new(10, 3) / 3_u8, Rational::new(10, 9));
        assert_eq!(Rational::new(4, 3) / 5_i32, Rational::new(4, 15));
        assert_eq!(Rational::new(1, 2) / 6, Rational::new(1, 12));
    }

    #[test]
    fn ordering() {
        assert!(Rational::new(1, 2) > Rational::new(1, 4));
        assert!(Rational::new(1, 2) == Rational::new(2, 4));
        assert!(Rational::new(3, 4) < Rational::new(8, 9));
    }

    #[test]
    fn strings() {
        let value = "10/2";
        let a: Rational = value.parse().unwrap();
        let b: String = format!("{}", a);
        assert_eq!(value, &b);
    }

    #[test]
    #[should_panic]
    fn panics() {
        Rational::new(0, 0) + Rational::new(0, 0);
    }
}