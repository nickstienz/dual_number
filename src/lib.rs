use std::ops::{Add, Mul, Sub};

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct DualNumber<T> {
    real: T,
    dual: T,
}

impl<T> DualNumber<T> {
    pub fn new(real: T, dual: T) -> Self {
        Self { real, dual }
    }
}

impl<T: Clone + Copy> DualNumber<T> {
    pub fn get_real(&self) -> T {
        self.real
    }

    pub fn get_dual(&self) -> T {
        self.dual
    }
}

impl<T: Add<Output = T>> Add for DualNumber<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self {
            real: self.real + other.real,
            dual: self.dual + other.dual,
        }
    }
}

impl<T: Mul<Output = T> + Add<Output = T> + Copy + Clone> Mul for DualNumber<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real * rhs.real,
            dual: (self.real * rhs.dual) + (self.dual * rhs.real),
        }
    }
}

impl<T: Sub<Output = T>> Sub for DualNumber<T> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real - rhs.real,
            dual: self.dual - rhs.dual,
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
    fn test_poly() {
        // 2x^2 + 5x - 3 | f(4) & f'(4)
        let x = DualNumber::new(4, 1);

        let c1 = DualNumber::new(2, 0);
        let c2 = DualNumber::new(5, 0);
        let c3 = DualNumber::new(3, 0);

        let result = c1 * x * x + c2 * x - c3;
        assert_eq!(result, DualNumber::new(49, 21));
    }
}
