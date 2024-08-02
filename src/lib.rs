//! # i24: A 24-bit Signed Integer Type
//!
//! The `i24` crate provides a 24-bit signed integer type for Rust, filling the gap between
//! `i16` and `i32`. This type is particularly useful in audio processing, certain embedded
//! systems, and other scenarios where 24-bit precision is required but 32 bits would be excessive.
//!
//! ## Features
//!
//! - Efficient 24-bit signed integer representation
//! - Seamless conversion to and from `i32`
//! - Support for basic arithmetic operations with overflow checking
//! - Bitwise operations
//! - Conversions from various byte representations (little-endian, big-endian, native)
//! - Implements common traits like `Debug`, `Display`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, and `Hash`
//!
//! This crate came about as a part of the [Wavers](https://crates.io/crates/wavers) project, which is a Wav file reader and writer for Rust.
//! The `i24` struct also has pyo3 bindings for use in Python. Enable the ``pyo3`` feature to use the pyo3 bindings.
//!
//! ## Usage
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! i24 = "1.0.1"
//! ```
//!
//! Then, in your Rust code:
//!
//! ```rust
//! use i24::i24;
//!
//! let a = i24::from_i32(1000);
//! let b = i24::from_i32(2000);
//! let c = a + b;
//! assert_eq!(c.to_i32(), 3000);
//! ```
//!
//! ## Safety and Limitations
//!
//! While `i24` strives to behave similarly to Rust's built-in integer types, there are some
//! important considerations:
//!
//! - The valid range for `i24` is [-8,388,608, 8,388,607].
//! - Overflow behavior in arithmetic operations matches that of `i32`.
//! - Bitwise operations are performed on the 24-bit representation.
//!
//! Always use checked arithmetic operations when dealing with untrusted input or when
//! overflow/underflow is a concern.
//!
//! ## Features
//! - **pyo3**: Enables the pyo3 bindings for the `i24` type.
//!
//! ## Contributing
//!
//! Contributions are welcome! Please feel free to submit a Pull Request. This really needs more testing and verification.
//!
//! ## License
//!
//! This project is licensed under MIT - see the [LICENSE](https://github.com/jmg049/i24/blob/main/LICENSE) file for details.
//!
use bytemuck::{Pod, Zeroable};
use num_traits::{Num, One, Zero};
use std::fmt;
use std::fmt::Display;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use std::{
    ops::{Neg, Not},
    str::FromStr,
};

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

/// Represents errors that can occur when working with the `i24` type.
#[derive(Debug, PartialEq, Eq)]
pub enum I24Error {
    /// An error occurred while parsing a string to an `i24`.
    ///
    /// This variant wraps the standard library's `ParseIntError`.
    ParseError(std::num::ParseIntError),

    /// The value is out of the valid range for an `i24`.
    ///
    /// Valid range for `i24` is [-8,388,608, 8,388,607].
    OutOfRange,
}

impl std::fmt::Display for I24Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            I24Error::ParseError(e) => write!(f, "Parse error: {}", e),
            I24Error::OutOfRange => write!(f, "Value out of range for i24"),
        }
    }
}

impl std::error::Error for I24Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            I24Error::ParseError(e) => Some(e),
            I24Error::OutOfRange => None,
        }
    }
}

impl From<std::num::ParseIntError> for I24Error {
    fn from(err: std::num::ParseIntError) -> Self {
        I24Error::ParseError(err)
    }
}

#[allow(non_camel_case_types)]
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "pyo3", pyclass)]
/// An experimental 24-bit signed integer type.
///
/// This type is a wrapper around ``[u8; 3]`` and is used to represent 24-bit audio samples.
/// It should not be used anywhere important. It is still unverified and experimental.
///
/// The type is not yet fully implemented and is not guaranteed to work.
/// Supports basic arithmetic operations and conversions to and from ``i32``.
///
/// Represents a 24-bit signed integer.
///
/// This struct stores the integer as three bytes in little-endian order.
pub struct i24 {
    /// The raw byte representation of the 24-bit integer.
    pub data: [u8; 3],
}

impl i24 {
    /// Converts the 24-bit integer to a 32-bit signed integer.
    ///
    /// This method performs sign extension if the 24-bit integer is negative.
    ///
    /// # Returns
    ///
    /// The 32-bit signed integer representation of this `i24`.
    pub const fn to_i32(self) -> i32 {
        let [a, b, c] = self.data;
        let value = i32::from_le_bytes([a, b, c, 0]);
        if value & 0x800000 != 0 {
            value | -0x1000000 // This is equivalent to 0xFF000000 but avoids the literal issue
        } else {
            value
        }
    }

    /// Creates an `i24` from a 32-bit signed integer.
    ///
    /// This method truncates the input to 24 bits if it's outside the valid range.
    ///
    /// # Arguments
    ///
    /// * `n` - The 32-bit signed integer to convert.
    ///
    /// # Returns
    ///
    /// An `i24` instance representing the input value.
    pub const fn from_i32(n: i32) -> Self {
        let bytes = n.to_le_bytes();
        Self {
            data: [bytes[0], bytes[1], bytes[2]],
        }
    }

    /// Creates an `i24` from three bytes in native endian order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer.
    ///
    /// # Returns
    ///
    /// An `i24` instance containing the input bytes.
    pub const fn from_ne_bytes(bytes: [u8; 3]) -> Self {
        Self { data: bytes }
    }

    /// Creates an `i24` from three bytes in **little-endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer in little-endian order.
    ///
    /// # Returns
    ///
    /// An `i24` instance containing the input bytes.
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        Self { data: bytes }
    }

    /// Creates an `i24` from three bytes in big-endian order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer in big-endian order.
    ///
    /// # Returns
    ///
    /// An `i24` instance with the bytes in little-endian order.
    pub const fn from_be_bytes(bytes: [u8; 3]) -> Self {
        Self {
            data: [bytes[2], bytes[1], bytes[0]],
        }
    }

    /// Performs checked addition.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i24` to add to this value.
    ///
    /// # Returns
    ///
    /// `Some(i24)` if the addition was successful, or `None` if it would overflow.
    pub fn checked_add(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_add(other.to_i32())
            .map(Self::from_i32)
    }

    /// Performs checked subtraction.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i24` to subtract from this value.
    ///
    /// # Returns
    ///
    /// `Some(i24)` if the subtraction was successful, or `None` if it would overflow.
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_sub(other.to_i32())
            .map(Self::from_i32)
    }

    /// Performs checked multiplication.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i24` to multiply with this value.
    ///
    /// # Returns
    ///
    /// `Some(i24)` if the multiplication was successful, or `None` if it would overflow.
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_mul(other.to_i32())
            .map(Self::from_i32)
    }

    /// Performs checked division.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i24` to divide this value by.
    ///
    /// # Returns
    ///
    /// `Some(i24)` if the division was successful, or `None` if the divisor is zero or if the division would overflow.
    pub fn checked_div(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_div(other.to_i32())
            .map(Self::from_i32)
    }
}

unsafe impl Zeroable for i24 {}
unsafe impl Pod for i24 {}

impl One for i24 {
    fn one() -> Self {
        i24::from_i32(1)
    }
}

impl Zero for i24 {
    fn zero() -> Self {
        i24::from_i32(0)
    }

    fn is_zero(&self) -> bool {
        i24::from_i32(0) == *self
    }
}

impl Num for i24 {
    type FromStrRadixErr = I24Error;
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        let i32_result = i32::from_str_radix(str, radix).map_err(I24Error::ParseError)?;
        if i32_result < -8388608 || i32_result > 8388607 {
            Err(I24Error::OutOfRange)
        } else {
            Ok(i24::from_i32(i32_result))
        }
    }
}

#[cfg(feature = "pyo3")]
use numpy::Element;

#[cfg(feature = "pyo3")]
unsafe impl Element for i24 {
    const IS_COPY: bool = true;

    fn get_dtype_bound(py: Python<'_>) -> Bound<'_, numpy::PyArrayDescr> {
        numpy::dtype_bound::<i24>(py)
    }
}

impl Add for i24 {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let result = self.to_i32().wrapping_add(other.to_i32());
        Self::from_i32(result)
    }
}

impl Sub for i24 {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let result = self.to_i32().wrapping_sub(other.to_i32());
        Self::from_i32(result)
    }
}

impl Mul for i24 {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let result = self.to_i32().wrapping_mul(other.to_i32());
        Self::from_i32(result)
    }
}

impl Div for i24 {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        let result = self.to_i32().wrapping_div(other.to_i32());
        Self::from_i32(result)
    }
}

impl Rem for i24 {
    type Output = Self;

    fn rem(self, other: Self) -> Self {
        let result = self.to_i32().wrapping_rem(other.to_i32());
        Self::from_i32(result)
    }
}

impl Neg for i24 {
    type Output = Self;

    fn neg(self) -> Self {
        let i32_result = self.to_i32().wrapping_neg();
        i24::from_i32(i32_result)
    }
}

impl Not for i24 {
    type Output = Self;

    fn not(self) -> Self {
        let i32_result = !self.to_i32();
        i24::from_i32(i32_result)
    }
}

impl BitAnd for i24 {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let result = self.to_i32() & rhs.to_i32();
        Self::from_i32(result)
    }
}

impl BitOr for i24 {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let result = self.to_i32() | rhs.to_i32();
        Self::from_i32(result)
    }
}

impl BitXor for i24 {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let result = self.to_i32() ^ rhs.to_i32();
        Self::from_i32(result)
    }
}

impl Shl<u32> for i24 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        let result = (self.to_i32() << rhs) & 0x00FFFFFF;
        if result & 0x800000 != 0 {
            Self::from_i32(result | -0x1000000)
        } else {
            Self::from_i32(result)
        }
    }
}

impl Shr<u32> for i24 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        let value = self.to_i32();
        let result = if value < 0 {
            ((value >> rhs) | (-1 << (24 - rhs))) & 0x00FFFFFF
        } else {
            (value >> rhs) & 0x00FFFFFF
        };
        Self::from_i32(result)
    }
}

impl Display for i24 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_i32())
    }
}

impl FromStr for i24 {
    type Err = I24Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let i32_result = i32::from_str(s)?;
        if i32_result < -8388608 || i32_result > 8388607 {
            Err(I24Error::OutOfRange)
        } else {
            Ok(i24::from_i32(i32_result))
        }
    }
}

macro_rules! implement_ops_assign {
    ($($trait_path:path { $($function_name:ident),* }),*) => {
        $(
            impl $trait_path for i24 {
                $(
                    fn $function_name(&mut self, other: Self){
                        let mut self_i32: i32 = self.to_i32();
                        let other_i32: i32 = other.to_i32();
                        self_i32.$function_name(other_i32);
                    }
                )*
            }
        )*
    };
}

macro_rules! implement_ops_assign_ref {
    ($($trait_path:path { $($function_name:ident),* }),*) => {
        $(
            impl $trait_path for &i24 {
                $(
                    fn $function_name(&mut self, other: Self){
                        let mut self_i32: i32 = self.to_i32();
                        let other_i32: i32 = other.to_i32();
                        self_i32.$function_name(other_i32);
                    }
                )*
            }
        )*
    };
}

implement_ops_assign!(
    AddAssign { add_assign },
    SubAssign { sub_assign },
    MulAssign { mul_assign },
    DivAssign { div_assign },
    RemAssign { rem_assign },
    BitAndAssign { bitand_assign },
    BitOrAssign { bitor_assign },
    BitXorAssign { bitxor_assign },
    ShlAssign { shl_assign },
    ShrAssign { shr_assign }
);

implement_ops_assign_ref!(
    AddAssign { add_assign },
    SubAssign { sub_assign },
    MulAssign { mul_assign },
    DivAssign { div_assign },
    RemAssign { rem_assign },
    BitAndAssign { bitand_assign },
    BitOrAssign { bitor_assign },
    BitXorAssign { bitxor_assign },
    ShlAssign { shl_assign },
    ShrAssign { shr_assign }
);

#[cfg(test)]
mod i24_tests {
    use super::*;

    #[test]
    fn test_arithmetic_operations() {
        let a = i24::from_i32(100);
        let b = i24::from_i32(50);

        assert_eq!((a + b).to_i32(), 150);
        assert_eq!((a - b).to_i32(), 50);
        assert_eq!((a * b).to_i32(), 5000);
        assert_eq!((a / b).to_i32(), 2);
        assert_eq!((a % b).to_i32(), 0);
    }

    #[test]
    fn test_bitwise_operations() {
        let a = i24::from_i32(0b101010);
        let b = i24::from_i32(0b110011);

        assert_eq!((a & b).to_i32(), 0b100010);
        assert_eq!((a | b).to_i32(), 0b111011);
        assert_eq!((a ^ b).to_i32(), 0b011001);
        assert_eq!((a << 2).to_i32(), 0b10101000);
        assert_eq!((a >> 2).to_i32(), 0b1010);
    }

    #[test]
    fn test_unary_operations() {
        let a = i24::from_i32(100);

        assert_eq!((-a).to_i32(), -100);
        assert_eq!((!a).to_i32(), -101);
    }

    #[test]
    fn test_from_i32() {
        assert_eq!(i24::from_i32(0).to_i32(), 0);
        assert_eq!(i24::from_i32(8388607).to_i32(), 8388607); // Max positive value
        assert_eq!(i24::from_i32(-8388608).to_i32(), -8388608); // Min negative value
    }

    #[test]
    fn test_from_bytes() {
        assert_eq!(i24::from_ne_bytes([0x01, 0x02, 0x03]).to_i32(), 0x030201);
        assert_eq!(i24::from_le_bytes([0x01, 0x02, 0x03]).to_i32(), 0x030201);
        assert_eq!(i24::from_be_bytes([0x01, 0x02, 0x03]).to_i32(), 0x010203);
    }

    #[test]
    fn test_to_i32() {
        let a = i24::from_ne_bytes([0xFF, 0xFF, 0x7F]);
        assert_eq!(a.to_i32(), 8388607); // Max positive value

        let b = i24::from_ne_bytes([0x00, 0x00, 0x80]);
        assert_eq!(b.to_i32(), -8388608); // Min negative value
    }

    #[test]
    fn test_zero_and_one() {
        assert_eq!(i24::zero().to_i32(), 0);
        assert_eq!(i24::one().to_i32(), 1);
    }
    #[test]
    fn test_from_str() {
        assert_eq!(i24::from_str("100").unwrap().to_i32(), 100);
        assert_eq!(i24::from_str("-100").unwrap().to_i32(), -100);
        assert_eq!(i24::from_str("8388607").unwrap().to_i32(), 8388607); // Max positive value
        assert_eq!(i24::from_str("-8388608").unwrap().to_i32(), -8388608); // Min negative value
        assert_eq!(i24::from_str("8388608").unwrap_err(), I24Error::OutOfRange);
        assert_eq!(i24::from_str("-8388609").unwrap_err(), I24Error::OutOfRange);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", i24::from_i32(100)), "100");
        assert_eq!(format!("{}", i24::from_i32(-100)), "-100");
    }

    #[test]
    fn test_wrapping_behavior() {
        let max = i24::from_i32(8388607);
        assert_eq!((max + i24::one()).to_i32(), -8388608);

        let min = i24::from_i32(-8388608);
        assert_eq!((min - i24::one()).to_i32(), 8388607);
    }

    #[test]
    fn test_shift_operations() {
        let a = i24::from_i32(0b1);

        // Left shift
        assert_eq!((a << 23).to_i32(), -8388608); // 0x800000, which is the minimum negative value
        assert_eq!((a << 24).to_i32(), 0); // Shifts out all bits

        // Right shift
        let b = i24::from_i32(-1); // All bits set
        assert_eq!((b >> 1).to_i32(), -1); // Sign extension
        assert_eq!((b >> 23).to_i32(), -1); // Still all bits set due to sign extension
        assert_eq!((b >> 24).to_i32(), -1); // No change after 23 bits

        // Edge case: maximum positive value
        let c = i24::from_i32(0x7FFFFF); // 8388607
        assert_eq!((c << 1).to_i32(), -2); // 0xFFFFFE in 24-bit, which is -2 when sign-extended

        // Edge case: minimum negative value
        let d = i24::from_i32(-0x800000); // -8388608
        assert_eq!((d >> 1).to_i32(), -4194304); // -0x400000

        // Additional test for left shift wrapping
        assert_eq!((c << 1).to_i32(), -2); // 0xFFFFFE
        assert_eq!((c << 2).to_i32(), -4); // 0xFFFFFC
        assert_eq!((c << 3).to_i32(), -8); // 0xFFFFF8
    }
}
