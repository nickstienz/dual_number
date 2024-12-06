use std::{
    fmt::{self, Display},
    ops::{Add, Mul, Neg, Sub},
};

/// `DualNumber` is the main struct used to work with dual numbers. It holds
/// two values of the same type. The type `T` must have all the traits defined
/// by each function which will typically be the numeric types like `i32`
/// or `f64` and such.
///
/// Using dual numbers is as easy as creating a `new` dual number and then operating
/// on it just like you would any other numeric type. There will also be extra
/// math functions that can be use on the dual numbers.
///
/// ```
/// use dual_number::DualNumber;
///
/// let x = DualNumber::new(5, 1);
///
/// // DualNumber supports (DualNumber * T) but not (T * DualNumber).
/// // This is in active development!
/// //let ans = 2 * x * x - 6 * x + -10;
/// //println!("f(x) = 2x^2 - 6x + -10 | f(5) & f'(5) = {}", ans);
/// ```
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct DualNumber<T> {
    real: T,
    dual: T,
}

impl<T> DualNumber<T> {
    /// The new function returns a DualNumber with the given type `T`.
    ///
    /// Both the real and dual part must be the same type in order for the
    /// function to return.
    ///
    /// ```
    /// use dual_number::DualNumber;
    ///
    /// let x = DualNumber::new(0, 0);
    /// ```
    pub fn new(real: T, dual: T) -> Self {
        Self { real, dual }
    }
}

impl<T: Clone + Copy> DualNumber<T> {
    /// Returns the real part of the dual number as a type `T` based on what it
    /// was created as.
    ///
    /// The value will be cloned or copied depending on what you or the
    /// compiler wants.
    ///
    /// ```
    /// use dual_number::DualNumber;
    ///
    /// let x = DualNumber::new(4, 1);
    /// let real = x.get_real();
    /// ```
    pub fn get_real(&self) -> T {
        self.real
    }

    /// Returns the dual part of the dual number as a type `T` based on what it
    /// was created as.
    ///
    /// The value will be cloned or copied depending on what you or the
    /// compiler wants.
    ///
    /// ```
    /// use dual_number::DualNumber;
    ///
    /// let x = DualNumber::new(4, 1);
    /// let dual = x.get_dual();
    /// ```
    pub fn get_dual(&self) -> T {
        self.dual
    }
}

/// Trait implementation for Display.
///
/// If the dual part of the number is 0, it will just write the real part
/// like any other type of `T` would. `5i32 -> "5"`
///
/// If there is a dual part, it will write the number using the normal
/// dual number notation like `"(5 + 3ɛ)"` or `"(5 - 3ɛ)"`.
impl<T: Display + PartialOrd<i32> + Neg<Output = T> + Copy + Clone> Display for DualNumber<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.dual == 0 {
            write!(f, "{}", self.real)
        } else if self.dual < 0 {
            write!(f, "({} - {}ɛ)", self.real, -self.dual)
        } else {
            write!(f, "({} + {}ɛ)", self.real, self.dual)
        }
    }
}

/// Trait implementation for `Add`.
///
/// Adds the rhs real part to the lhs real part and adds the rhs dual part to
/// the lhs dual part.
impl<T: Add<Output = T>> Add for DualNumber<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real + rhs.real,
            dual: self.dual + rhs.dual,
        }
    }
}

/// Trait implementation for `Add<T>`.
///
/// Adds the rhs to the lhs real part and does nothing to the dual part.
impl<T: Add<Output = T>> Add<T> for DualNumber<T> {
    type Output = Self;

    fn add(self, rhs: T) -> Self::Output {
        Self {
            real: self.real + rhs,
            dual: self.dual,
        }
    }
}

/// Trait implementation for Sub.
///
/// Subtracts the lhs real part from the rhs real part
/// and subtracts the lhs dual part from the rhs dual part.
impl<T: Sub<Output = T>> Sub for DualNumber<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real - rhs.real,
            dual: self.dual - rhs.dual,
        }
    }
}

/// Trait implementation for Mul.
///
/// The real part is the lhs real part multiplied by the rhs real part.
impl<T: Mul<Output = T> + Add<Output = T> + Copy + Clone> Mul for DualNumber<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real * rhs.real,
            dual: (self.real * rhs.dual) + (self.dual * rhs.real),
        }
    }
}

/// Trait implementation for `Mul<T>`.
///
/// The real part is the lhs real part multiplied by the rhs real part.
impl<T: Mul<Output = T> + Add<Output = T> + Copy + Clone> Mul<T> for DualNumber<T> {
    type Output = Self;

    fn mul(self, rhs: T) -> Self::Output {
        Self {
            real: self.real * rhs,
            dual: self.dual * rhs,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let x = DualNumber::new(3, 4);
        let y = DualNumber::new(1, 2);

        let result = x + y;
        assert_eq!(result, DualNumber::new(4, 6));
    }

    #[test]
    fn test_add_t() {
        let x = DualNumber::new(3, 2);

        let result = x + 5;
        assert_eq!(result, DualNumber::new(8, 2));
    }

    #[test]
    fn test_sub() {
        let x = DualNumber::new(3, 4);
        let y = DualNumber::new(1, 2);

        let result = x - y;
        assert_eq!(result, DualNumber::new(2, 2));
    }

    #[test]
    fn test_mul() {
        let x = DualNumber::new(3, 4);
        let y = DualNumber::new(1, 2);

        let result = x * y;
        assert_eq!(result, DualNumber::new(3, 10));
    }

    #[test]
    fn test_mul_t() {
        let x = DualNumber::new(3, 2);

        let result = x * 5;
        assert_eq!(result, DualNumber::new(15, 10));
    }

    #[test]
    fn test_poly_1() {
        // 2x^2 + 5x - 3 | f(4) & f'(4)
        let x = DualNumber::new(4, 1);

        let c1 = DualNumber::new(2, 0);
        let c2 = DualNumber::new(5, 0);
        let c3 = DualNumber::new(3, 0);

        let result = c1 * x * x + c2 * x - c3;
        assert_eq!(result, DualNumber::new(49, 21));
    }

    #[test]
    fn test_poly_2() {
        // x^2 + 2 | f(0) & f'(0)
        let x = DualNumber::new(0, 1);

        let c = DualNumber::new(2, 0);

        let result = x * x + c;
        assert_eq!(result, DualNumber::new(2, 0));
    }
}
