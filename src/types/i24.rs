#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use bytemuck::{NoUninit, Pod, Zeroable};
use core::fmt;
use core::fmt::{Debug, Display, LowerHex, Octal, UpperHex};
use core::hash::{Hash, Hasher};
use core::num::ParseIntError;
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use core::{
    ops::{Neg, Not},
    str::FromStr,
};

#[cfg(feature = "num-cast")]
use num_traits::NumCast;
use num_traits::{FromPrimitive, Num, One, Signed, ToBytes, ToPrimitive, Zero};

use crate::repr::I24Repr;
use crate::{TryFromIntError, i24, out_of_range};

#[allow(non_camel_case_types)]
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
/// A signed 24-bit integer type.
///
/// The `I24` type represents a 24-bit signed integer in two's complement format. It fills the gap between
/// `i16` and `i32`, offering reduced memory usage while preserving a larger numeric range than `i16`.
///
/// This type is particularly suited to applications such as audio processing, binary file manipulation,
/// embedded systems, or networking protocols where 24-bit integers are common.
///
/// ## Range
///
/// The valid value range is:
///
/// ```text
///   MIN = -8_388_608   // -2^23
///   MAX =  8_388_607   //  2^23 - 1
/// ```
///
/// Arithmetic operations are implemented to match Rust’s standard integer behavior,
/// including overflow and checked variants.
///
/// ## Memory Layout and Safety
///
/// `I24` is implemented as a `#[repr(transparent)]` wrapper around a 4-byte internal representation.
/// Although the logical width is 24 bits, one additional byte is used for alignment and padding control.
///
/// This struct:
///
/// - Contains **no uninitialized or padding bytes**
/// - Is **safe to use** with [`bytemuck::NoUninit`](https://docs.rs/bytemuck/latest/bytemuck/trait.NoUninit.html)
/// - Can be cast safely with [`bytemuck::cast_slice`] for use in FFI and low-level applications
///
/// The layout is verified via compile-time assertions to ensure portability and correctness.
///
/// ## Binary Serialization
///
/// Although `I24` occupies 4 bytes in memory, binary formats (e.g., WAV files, network protocols) often
/// store 24-bit integers in a 3-byte representation. To support this:
///
/// - `I24` provides [`I24::from_be_bytes`], [`I24::from_le_bytes`], and [`I24::from_ne_bytes`] methods for constructing
///   values from 3-byte on-disk representations
/// - Corresponding [`I24::to_be_bytes`], [`I24::to_le_bytes`], and [`I24::to_ne_bytes`] methods convert to 3-byte representations
///
/// For efficient bulk deserialization, use the inherent methods on `I24`.
///
///  Note: Requires the ``alloc`` feature to be enabled.
///
/// ```
/// # #[cfg(feature = "alloc")] {
/// use i24::I24;
/// let raw: &[u8] = &[0x00, 0x00, 0x01, 0xFF, 0xFF, 0xFF];
/// let values = I24::read_i24s_be(raw).expect("Test value should convert successfully");
/// assert_eq!(values[0].to_i32(), 1);
/// assert_eq!(values[1].to_i32(), -1);
/// # }
/// ```
///
/// ## Usage Notes
///
/// - Use the `i24!` macro for compile-time checked construction
/// - Use `.to_i32()` to convert to standard Rust types
/// - Supports traits like `Add`, `Sub`, `Display`, `Hash`, `Ord`, and `FromStr`
///
/// ## Features
///
/// - **`serde`**: Enables `Serialize` and `Deserialize` support via JSON or other formats
/// - **`pyo3`**: Exposes the `I24` type to Python via `PyO3` bindings (as `I24`)
/// - **`alloc`**: Enables `I24DiskMethods` for efficient bulk serialization/deserialization
pub struct I24(I24Repr);

// Safety: repr(transparent) and so if I24Repr is Zeroable so should I24 be
unsafe impl Zeroable for I24 where I24Repr: Zeroable {}

// Safety: repr(transparent) and so if I24Repr is NoUninit so should I24 be
// Must be NoUninit due to the padding byte.
unsafe impl NoUninit for I24 where I24Repr: NoUninit {}

impl FromPrimitive for I24
where
    I24Repr: FromPrimitive,
{
    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        I24Repr::from_i64(n).map(Self)
    }

    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        I24Repr::from_u64(n).map(Self)
    }
}

impl I24 {
    /// The size of this integer type in bits
    pub const BITS: u32 = 24;

    /// The smallest value that can be represented by this integer type (-2<sup>23</sup>)
    pub const MIN: Self = i24!(I24Repr::MIN);

    /// The largest value that can be represented by this integer type (2<sup>23</sup> − 1).
    pub const MAX: Self = i24!(I24Repr::MAX);

    /// Creates a new `I24` with all bits set to zero.
    pub const ZERO: Self = i24!(I24Repr::ZERO);

    /// Returns a reference to the underlying 32-bit representation.
    ///
    /// The 24-bit value is stored in the lower 24 bits, with the upper 8 bits guaranteed to be zero.
    /// This method provides direct access to the internal bit representation for advanced use cases.
    #[inline]
    #[must_use]
    pub const fn as_bits(&self) -> &u32 {
        self.0.as_bits()
    }

    /// Returns the underlying 32-bit representation.
    ///
    /// The 24-bit value is stored in the lower 24 bits, with the upper 8 bits guaranteed to be zero.
    /// This method extracts the internal bit representation for advanced use cases.
    #[inline]
    #[must_use]
    pub const fn to_bits(self) -> u32 {
        self.0.to_bits()
    }

    /// Safety: see `I24Repr::from_bits`
    #[inline]
    const unsafe fn from_bits(bits: u32) -> Self {
        Self(unsafe { I24Repr::from_bits(bits) })
    }

    /// same as `Self::from_bits` but always truncates
    #[inline]
    const fn from_bits_truncate(bits: u32) -> Self {
        // the most significant byte is zeroed out
        Self(unsafe { I24Repr::from_bits(bits & I24Repr::BITS_MASK) })
    }

    /// Converts the 24-bit integer to a 32-bit signed integer.
    ///
    /// This method performs sign extension if the 24-bit integer is negative.
    ///
    /// # Returns
    ///
    /// The 32-bit signed integer representation of this `I24`.
    #[inline]
    #[must_use]
    pub const fn to_i32(self) -> i32 {
        self.0.to_i32()
    }

    /// Creates an `I24` from a 32-bit signed integer.
    ///
    /// This method truncates the input to 24 bits if it's outside the valid range.
    ///
    /// # Arguments
    ///
    /// * `n` - The 32-bit signed integer to convert.
    ///
    /// # Returns
    ///
    /// An `I24` instance representing the input value.
    #[inline]
    #[must_use]
    pub const fn wrapping_from_i32(n: i32) -> Self {
        Self(I24Repr::wrapping_from_i32(n))
    }

    /// Creates an `I24` from a 32-bit signed integer.
    ///
    /// This method saturates the input if it's outside the valid range.
    ///
    /// # Arguments
    ///
    /// * `n` - The 32-bit signed integer to convert.
    ///
    /// # Returns
    ///
    /// An `I24` instance representing the input value.
    #[inline]
    #[must_use]
    pub const fn saturating_from_i32(n: i32) -> Self {
        Self(I24Repr::saturating_from_i32(n))
    }

    /// Reverses the byte order of the integer.
    #[inline]
    #[must_use]
    pub const fn swap_bytes(self) -> Self {
        Self(self.0.swap_bytes())
    }

    /// Converts self to little endian from the target's endianness.
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    #[inline]
    #[must_use]
    pub const fn to_le(self) -> Self {
        Self(self.0.to_le())
    }

    /// Converts self to big endian from the target's endianness.
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    #[inline]
    #[must_use]
    pub const fn to_be(self) -> Self {
        Self(self.0.to_be())
    }

    /// Return the memory representation of this integer as a byte array in native byte order.
    /// As the target platform's native endianness is used,
    /// portable code should use `to_be_bytes` or `to_le_bytes`, as appropriate, instead.
    #[inline]
    #[must_use]
    pub const fn to_ne_bytes(self) -> [u8; 3] {
        self.0.to_ne_bytes()
    }

    /// Create a native endian integer value from its representation as a byte array in little endian.
    #[inline]
    #[must_use]
    pub const fn to_le_bytes(self) -> [u8; 3] {
        self.0.to_le_bytes()
    }

    /// Return the memory representation of this integer as a byte array in big-endian (network) byte order.
    #[inline]
    #[must_use]
    pub const fn to_be_bytes(self) -> [u8; 3] {
        self.0.to_be_bytes()
    }

    /// Creates an `I24` from three bytes in **native endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer.
    ///
    /// # Returns
    ///
    /// An `I24` instance containing the input bytes.
    #[inline]
    #[must_use]
    pub const fn from_ne_bytes(bytes: [u8; 3]) -> Self {
        Self(I24Repr::from_ne_bytes(bytes))
    }

    /// Creates an `I24` from three bytes in **little-endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer in little-endian order.
    ///
    /// # Returns
    ///
    /// An `I24` instance containing the input bytes.
    #[inline]
    #[must_use]
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        Self(I24Repr::from_le_bytes(bytes))
    }

    /// Creates an `I24` from three bytes in **big-endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer in big-endian order.
    ///
    /// # Returns
    ///
    /// An `I24` instance containing the input bytes interpreted as big-endian.
    #[inline]
    #[must_use]
    pub const fn from_be_bytes(bytes: [u8; 3]) -> Self {
        Self(I24Repr::from_be_bytes(bytes))
    }

    /// Performs checked addition.
    ///
    /// # Arguments
    ///
    /// * `other` - The `I24` to add to this value.
    ///
    /// # Returns
    ///
    /// `Some(I24)` if the addition was successful, or `None` if it would overflow.
    pub fn checked_add(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_add(other.to_i32())
            .and_then(Self::try_from_i32)
    }

    /// Performs checked subtraction.
    ///
    /// # Arguments
    ///
    /// * `other` - The `I24` to subtract from this value.
    ///
    /// # Returns
    ///
    /// `Some(I24)` if the subtraction was successful, or `None` if it would overflow.
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_sub(other.to_i32())
            .and_then(Self::try_from_i32)
    }

    /// Performs checked multiplication.
    ///
    /// # Arguments
    ///
    /// * `other` - The `I24` to multiply with this value.
    ///
    /// # Returns
    ///
    /// `Some(I24)` if the multiplication was successful, or `None` if it would overflow.
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_mul(other.to_i32())
            .and_then(Self::try_from_i32)
    }

    /// Performs checked division.
    ///
    /// # Arguments
    ///
    /// * `other` - The `I24` to divide this value by.
    ///
    /// # Returns
    ///
    /// `Some(I24)` if the division was successful, or `None` if the divisor is zero or if the division would overflow.
    pub fn checked_div(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_div(other.to_i32())
            .and_then(Self::try_from_i32)
    }

    /// Performs checked integer remainder.
    ///
    /// # Arguments
    ///
    /// * `other` - The `I24` to divide this value by.
    ///
    /// # Returns
    ///
    /// `Some(I24)` if the remainder operation was successful, or `None` if the divisor is zero or if the division would overflow.
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_rem(other.to_i32())
            .and_then(Self::try_from_i32)
    }

    /// Performs checked negation.
    ///
    /// # Returns
    ///
    /// `Some(I24)` if the negation was successful, or `None` if it would overflow.
    /// This happens when negating `I24::MIN` (since `-I24::MIN` cannot be represented in 24 bits).
    pub fn checked_neg(self) -> Option<Self> {
        self.to_i32().checked_neg().and_then(Self::try_from_i32)
    }

    /// Computes the absolute value of `self`.
    ///
    /// # Returns
    ///
    /// The absolute value of `self`. Note that `I24::MIN.abs()` will overflow and wrap to `I24::MIN`.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").abs(), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(-10).expect("Test value should convert successfully").abs(), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn abs(self) -> Self {
        if self.to_i32() < 0 { -self } else { self }
    }

    /// Computes the absolute value of `self` without any wrapping or panicking.
    ///
    /// # Returns
    ///
    /// The absolute value of `self`. For `I24::MIN`, returns `I24::MIN` (wrapping behavior).
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").wrapping_abs(), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(-10).expect("Test value should convert successfully").wrapping_abs(), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.wrapping_abs(), I24::MIN); // Wraps around
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_abs(self) -> Self {
        if self.to_i32() < 0 { -self } else { self }
    }

    /// Computes the absolute value of `self`, saturating at the bounds instead of overflowing.
    ///
    /// # Returns
    ///
    /// The absolute value of `self`. For `I24::MIN`, returns `I24::MAX` (saturating behavior).
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").saturating_abs(), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(-10).expect("Test value should convert successfully").saturating_abs(), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.saturating_abs(), I24::MAX); // Saturates to MAX
    /// ```
    #[inline]
    #[must_use]
    pub fn saturating_abs(self) -> Self {
        if self == Self::MIN {
            Self::MAX
        } else if self.to_i32() < 0 {
            -self
        } else {
            self
        }
    }

    /// Returns a number representing the sign of `self`.
    ///
    /// # Returns
    ///
    /// * `1` if `self` is positive
    /// * `0` if `self` is zero
    /// * `-1` if `self` is negative
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").signum(), I24::try_from_i32(1).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(0).expect("Test value should convert successfully").signum(), I24::try_from_i32(0).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(-10).expect("Test value should convert successfully").signum(), I24::try_from_i32(-1).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn signum(self) -> Self {
        let val = self.to_i32();
        match val.cmp(&0) {
            core::cmp::Ordering::Greater => Self::one(),
            core::cmp::Ordering::Less => -Self::one(),
            core::cmp::Ordering::Equal => Self::zero(),
        }
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero or positive.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert!(!I24::try_from_i32(10).expect("Test value should convert successfully").is_negative());
    /// assert!(!I24::try_from_i32(0).expect("Test value should convert successfully").is_negative());
    /// assert!(I24::try_from_i32(-10).expect("Test value should convert successfully").is_negative());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_negative(self) -> bool {
        self.to_i32() < 0
    }

    /// Returns `true` if `self` is positive and `false` if the number is zero or negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert!(I24::try_from_i32(10).expect("Test value should convert successfully").is_positive());
    /// assert!(!I24::try_from_i32(0).expect("Test value should convert successfully").is_positive());
    /// assert!(!I24::try_from_i32(-10).expect("Test value should convert successfully").is_positive());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.to_i32() > 0
    }

    /// The positive difference of two numbers.
    ///
    /// Returns zero if the number is less than or equal to the other,
    /// otherwise the difference between `self` and `other` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").abs_sub(&I24::try_from_i32(5).expect("Test value should convert successfully")), I24::try_from_i32(5).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(5).expect("Test value should convert successfully").abs_sub(&I24::try_from_i32(10).expect("Test value should convert successfully")), I24::try_from_i32(0).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").abs_sub(&I24::try_from_i32(10).expect("Test value should convert successfully")), I24::try_from_i32(0).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn abs_sub(&self, other: &Self) -> Self {
        if *self <= *other {
            Self::zero()
        } else {
            *self - *other
        }
    }

    /// Restricts the value to a certain interval.
    ///
    /// Returns `max` if `self` is greater than `max`, and `min` if `self` is less than `min`.
    /// Otherwise, returns `self`.
    ///
    /// # Panics
    ///
    /// Panics if `min > max`.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(-3).expect("Test value should convert successfully").clamp(I24::try_from_i32(-2).expect("Test value should convert successfully"), I24::try_from_i32(1).expect("Test value should convert successfully")), I24::try_from_i32(-2).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(0).expect("Test value should convert successfully").clamp(I24::try_from_i32(-2).expect("Test value should convert successfully"), I24::try_from_i32(1).expect("Test value should convert successfully")), I24::try_from_i32(0).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(2).expect("Test value should convert successfully").clamp(I24::try_from_i32(-2).expect("Test value should convert successfully"), I24::try_from_i32(1).expect("Test value should convert successfully")), I24::try_from_i32(1).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn clamp(self, min: Self, max: Self) -> Self {
        assert!(min <= max);
        if self < min {
            min
        } else if self > max {
            max
        } else {
            self
        }
    }

    /// Computes the minimum of `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(1).expect("Test value should convert successfully").min(I24::try_from_i32(2).expect("Test value should convert successfully")), I24::try_from_i32(1).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(2).expect("Test value should convert successfully").min(I24::try_from_i32(1).expect("Test value should convert successfully")), I24::try_from_i32(1).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn min(self, other: Self) -> Self {
        if self <= other { self } else { other }
    }

    /// Computes the maximum of `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(1).expect("Test value should convert successfully").max(I24::try_from_i32(2).expect("Test value should convert successfully")), I24::try_from_i32(2).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(2).expect("Test value should convert successfully").max(I24::try_from_i32(1).expect("Test value should convert successfully")), I24::try_from_i32(2).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn max(self, other: Self) -> Self {
        if self >= other { self } else { other }
    }

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").wrapping_add(I24::try_from_i32(27).expect("Test value should convert successfully")), I24::try_from_i32(127).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MAX.wrapping_add(I24::try_from_i32(2).expect("Test value should convert successfully")), I24::MIN + I24::try_from_i32(1).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_add(self, rhs: Self) -> Self {
        self + rhs // Addition already wraps
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").wrapping_sub(I24::try_from_i32(100).expect("Test value should convert successfully")), I24::try_from_i32(0).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.wrapping_sub(I24::try_from_i32(1).expect("Test value should convert successfully")), I24::MAX);
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_sub(self, rhs: Self) -> Self {
        self - rhs // Subtraction already wraps
    }

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").wrapping_mul(I24::try_from_i32(12).expect("Test value should convert successfully")), I24::try_from_i32(120).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(25).expect("Test value should convert successfully").wrapping_mul(I24::try_from_i32(4).expect("Test value should convert successfully")), I24::try_from_i32(100).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_mul(self, rhs: Self) -> Self {
        self * rhs // Multiplication already wraps
    }

    /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at the boundary of the type.
    ///
    /// The only case where wrapping can occur is when dividing the minimum value by -1, which would
    /// overflow but instead wraps to the minimum value.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").wrapping_div(I24::try_from_i32(10).expect("Test value should convert successfully")), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.wrapping_div(I24::try_from_i32(-1).expect("Test value should convert successfully")), I24::MIN); // Wraps around
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        self / rhs // Division already wraps for the MIN / -1 case
    }

    /// Wrapping (modular) remainder. Computes `self % rhs`, wrapping around at the boundary of the type.
    ///
    /// The only case where wrapping can occur is when computing the remainder of the minimum value
    /// divided by -1, which would overflow but instead wraps to 0.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").wrapping_rem(I24::try_from_i32(10).expect("Test value should convert successfully")), I24::try_from_i32(0).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.wrapping_rem(I24::try_from_i32(-1).expect("Test value should convert successfully")), I24::try_from_i32(0).expect("Test value should convert successfully")); // Wraps around
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        self % rhs // Remainder already wraps for the MIN % -1 case
    }

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary of the type.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").wrapping_neg(), I24::try_from_i32(-100).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.wrapping_neg(), I24::MIN); // Wraps around
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_neg(self) -> Self {
        -self // Negation already wraps
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").saturating_add(I24::try_from_i32(1).expect("Test value should convert successfully")), I24::try_from_i32(101).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MAX.saturating_add(I24::try_from_i32(1).expect("Test value should convert successfully")), I24::MAX);
    /// assert_eq!(I24::MIN.saturating_add(I24::try_from_i32(-1).expect("Test value should convert successfully")), I24::MIN);
    /// ```
    #[inline]
    #[must_use]
    pub fn saturating_add(self, rhs: Self) -> Self {
        self.to_i32()
            .saturating_add(rhs.to_i32())
            .try_into()
            .unwrap_or_else(|_| {
                if rhs.to_i32() > 0 {
                    Self::MAX
                } else {
                    Self::MIN
                }
            })
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").saturating_sub(I24::try_from_i32(127).expect("Test value should convert successfully")), I24::try_from_i32(-27).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.saturating_sub(I24::try_from_i32(1).expect("Test value should convert successfully")), I24::MIN);
    /// assert_eq!(I24::MAX.saturating_sub(I24::try_from_i32(-1).expect("Test value should convert successfully")), I24::MAX);
    /// ```
    #[inline]
    #[must_use]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        self.to_i32()
            .saturating_sub(rhs.to_i32())
            .try_into()
            .unwrap_or_else(|_| {
                if rhs.to_i32() < 0 {
                    Self::MAX
                } else {
                    Self::MIN
                }
            })
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(10).expect("Test value should convert successfully").saturating_mul(I24::try_from_i32(12).expect("Test value should convert successfully")), I24::try_from_i32(120).expect("Test value should convert successfully"));
    /// assert_eq!(I24::try_from_i32(1000000).expect("Test value should convert successfully").saturating_mul(I24::try_from_i32(10).expect("Test value should convert successfully")), I24::MAX);
    /// assert_eq!(I24::try_from_i32(-1000000).expect("Test value should convert successfully").saturating_mul(I24::try_from_i32(10).expect("Test value should convert successfully")), I24::MIN);
    /// ```
    #[inline]
    #[must_use]
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        let result = self.to_i32().saturating_mul(rhs.to_i32());
        Self::saturating_from_i32(result)
    }

    /// Saturating integer division. Computes `self / rhs`, saturating at the numeric bounds.
    ///
    /// The only case where saturation can occur is when dividing the minimum value by -1,
    /// which would overflow but instead saturates to the maximum value.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").saturating_div(I24::try_from_i32(10).expect("Test value should convert successfully")), I24::try_from_i32(10).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.saturating_div(I24::try_from_i32(-1).expect("Test value should convert successfully")), I24::MAX); // Saturates
    /// ```
    #[inline]
    #[must_use]
    pub fn saturating_div(self, rhs: Self) -> Self {
        if self == Self::MIN && rhs.to_i32() == -1 {
            Self::MAX
        } else {
            self / rhs
        }
    }

    /// Saturating integer negation. Computes `-self`, saturating at the numeric bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;
    /// assert_eq!(I24::try_from_i32(100).expect("Test value should convert successfully").saturating_neg(), I24::try_from_i32(-100).expect("Test value should convert successfully"));
    /// assert_eq!(I24::MIN.saturating_neg(), I24::MAX); // Saturates
    /// ```
    #[inline]
    #[must_use]
    pub fn saturating_neg(self) -> Self {
        if self == Self::MIN { Self::MAX } else { -self }
    }

    /// Converts a byte slice in little-endian order to a Vec of I24 values.
    ///
    /// This method interprets the input byte slice as a sequence of 24-bit unsigned integers
    /// stored in little-endian format (least significant byte first). Each `I24` value
    /// requires exactly 3 bytes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice containing 24-bit unsigned integers in little-endian format.
    ///   The length must be a multiple of 3.
    ///
    /// # Returns
    ///
    /// `Some(Vec<I24>)` containing the parsed values, or `None` if the input slice
    /// length is not a multiple of 3.
    #[cfg(feature = "alloc")]
    pub fn read_i24s_le(bytes: &[u8]) -> Option<Vec<I24>> {
        if !bytes.len().is_multiple_of(3) {
            return None;
        }

        let mut result = Vec::with_capacity(bytes.len() / 3);

        bytes.chunks_exact(3).for_each(|chunk| {
            result.push(I24::from_le_bytes([chunk[0], chunk[1], chunk[2]]));
        });

        Some(result)
    }

    /// Converts a byte slice in little-endian order to a slice of I24 values.
    ///
    /// This method interprets the input byte slice as a sequence of 24-bit integers
    /// stored in little-endian format. Each `I24` value requires exactly 3 bytes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice containing 24-bit integers in little-endian format.
    ///   The length must be a multiple of 3.
    ///
    /// # Returns
    ///
    /// `Some(&[I24])` containing a slice view of the parsed values, or `None` if the input slice
    /// length is not a multiple of 3.
    #[cfg(feature = "alloc")]
    pub const fn read_i24s_le_slice(bytes: &[u8]) -> Option<&[I24]> {
        if !bytes.len().is_multiple_of(3) {
            return None;
        }

        let result =
            unsafe { core::slice::from_raw_parts(bytes.as_ptr() as *const I24, bytes.len() / 3) };

        Some(result)
    }

    /// Converts a byte slice in big-endian order to a Vec of I24 values.
    ///
    /// This method interprets the input byte slice as a sequence of 24-bit unsigned integers
    /// stored in big-endian format (most significant byte first). Each `I24` value
    /// requires exactly 3 bytes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice containing 24-bit unsigned integers in big-endian format.
    ///   The length must be a multiple of 3.
    ///
    /// # Returns
    ///
    /// `Some(Vec<I24>)` containing the parsed values, or `None` if the input slice
    /// length is not a multiple of 3.
    #[cfg(feature = "alloc")]
    pub fn read_i24s_be(bytes: &[u8]) -> Option<Vec<I24>> {
        if !bytes.len().is_multiple_of(3) {
            return None;
        }

        let mut result = Vec::with_capacity(bytes.len() / 3);

        bytes.chunks_exact(3).for_each(|chunk| {
            result.push(I24::from_be_bytes([chunk[0], chunk[1], chunk[2]]));
        });

        Some(result)
    }

    /// Reads multiple `I24` values from a byte slice in little-endian format without length validation.
    ///
    /// # Safety
    ///
    /// The input slice length must be a multiple of 3 bytes. Undefined behavior will occur
    /// if this precondition is not met.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice whose length must be a multiple of 3
    ///
    /// # Returns
    ///
    /// A vector containing the parsed `I24` values.
    #[cfg(feature = "alloc")]
    pub unsafe fn read_i24s_le_unchecked(bytes: &[u8]) -> Vec<I24> {
        debug_assert!(bytes.len().is_multiple_of(3));
        let chunks: &[I24Bytes] = bytemuck::cast_slice(bytes);
        chunks.iter().map(|b| b.to_i24_le()).collect()
    }

    #[cfg(feature = "alloc")]
    /// Reads multiple `I24` values from a byte slice in little-endian format without length validation.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `bytes.len()` is a multiple of 3.
    pub unsafe fn read_i24s_le_slice_unchecked(bytes: &[u8]) -> &[I24] {
        debug_assert!(bytes.len().is_multiple_of(3));
        unsafe { core::slice::from_raw_parts(bytes.as_ptr() as *const I24, bytes.len() / 3) }
    }

    /// Reads multiple `I24` values from a byte slice in big-endian format without length validation.
    ///
    /// # Safety
    ///
    /// The input slice length must be a multiple of 3 bytes. Undefined behavior will occur
    /// if this precondition is not met.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice whose length must be a multiple of 3
    ///
    /// # Returns
    ///
    /// A vector containing the parsed `I24` values.
    #[cfg(feature = "alloc")]
    pub unsafe fn read_i24s_be_unchecked(bytes: &[u8]) -> Vec<I24> {
        debug_assert!(bytes.len().is_multiple_of(3));
        let chunks: &[I24Bytes] = bytemuck::cast_slice(bytes);
        chunks.iter().map(|b| b.to_i24_be()).collect()
    }

    /// Converts a slice of I24 values to a Vec of bytes in little-endian order.
    #[cfg(feature = "alloc")]
    pub fn write_i24s_le(values: &[I24]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(values.len() * 3);
        for &value in values {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        bytes
    }

    /// Converts a slice of I24 values to a Vec of bytes in big-endian order.
    #[cfg(feature = "alloc")]
    pub fn write_i24s_be(values: &[I24]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(values.len() * 3);
        for &value in values {
            bytes.extend_from_slice(&value.to_be_bytes());
        }
        bytes
    }

    /// Reads multiple `I24` values from a byte slice in native-endian format.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice whose length must be a multiple of 3
    ///
    /// # Returns
    ///
    /// `Some(Vec<I24>)` containing the parsed values, or `None` if the input slice
    /// length is not a multiple of 3.
    #[cfg(feature = "alloc")]
    pub fn read_i24s_ne(bytes: &[u8]) -> Option<Vec<I24>> {
        if !bytes.len().is_multiple_of(3) {
            return None;
        }

        let mut result = Vec::with_capacity(bytes.len() / 3);

        bytes.chunks_exact(3).for_each(|chunk| {
            result.push(I24::from_ne_bytes([chunk[0], chunk[1], chunk[2]]));
        });

        Some(result)
    }

    /// Converts a slice of I24 values to a Vec of bytes in native-endian order.
    #[cfg(feature = "alloc")]
    pub fn write_i24s_ne(values: &[I24]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(values.len() * 3);
        for &value in values {
            bytes.extend_from_slice(&value.to_ne_bytes());
        }
        bytes
    }
}

macro_rules! impl_bin_op {
    ($(impl $op: ident = $assign: ident $assign_fn: ident { $($impl: tt)* })+) => {$(
        impl_bin_op!(impl $op = $assign $assign_fn for I24 { $($impl)* });
        impl_bin_op!(impl $op = $assign $assign_fn for &I24 { $($impl)* });
    )+};

    (impl $op: ident = $assign: ident $assign_fn: ident for $ty:ty {
         fn $meth: ident($self: tt, $other: ident) {
            $($impl: tt)*
         }
    }) => {
        impl $op<$ty> for I24 {
            type Output = Self;

            #[inline]
            fn $meth($self, $other: $ty) -> Self {
                $($impl)*
            }
        }

        impl $op<$ty> for &I24 {
            type Output = I24;

            #[inline]
            fn $meth(self, other: $ty) -> I24 {
                <I24 as $op<$ty>>::$meth(*self, other)
            }
        }

        impl $assign<$ty> for I24 {
            #[inline]
            fn $assign_fn(&mut self, rhs: $ty) {
                *self = $op::$meth(*self, rhs)
            }
        }
    };
}

impl_bin_op! {
    impl Add = AddAssign add_assign {
        fn add(self, other) {
            // we use two's complement and so signed and unsigned addition are strictly the same
            // so no need to cast to an i32
            Self::from_bits_truncate(self.to_bits().wrapping_add(other.to_bits()))
        }
    }

    impl Sub = SubAssign sub_assign {
        fn sub(self, other) {
            // we use two's complement and so signed and unsigned subtraction are strictly the same
            // so no need to cast to an i32
            Self::from_bits_truncate(self.to_bits().wrapping_sub(other.to_bits()))
        }
    }

    impl Mul = MulAssign mul_assign {
        fn mul(self, other) {
            // we use two's complement and so signed and unsigned non-widening multiplication are strictly the same
            // so no need to cast to an i32
            Self::from_bits_truncate(self.to_bits().wrapping_mul(other.to_bits()))
        }
    }

    impl Div = DivAssign div_assign {
        fn div(self, other) {
            let other_val = unsafe { I24::from_bits(other.to_bits()) };
            let result = <I24>::to_i32(self).wrapping_div(<I24>::to_i32(other_val));
            Self::wrapping_from_i32(result)
        }
    }

    impl Rem = RemAssign rem_assign {
        fn rem(self, other) {
            let other_val = unsafe { I24::from_bits(other.to_bits()) };
            let result = <I24>::to_i32(self).wrapping_rem(<I24>::to_i32(other_val));
            Self::wrapping_from_i32(result)
        }
    }


    impl BitAnd = BitAndAssign bitand_assign {
        fn bitand(self, rhs) {
            let bits = self.to_bits() & rhs.to_bits();
            // Safety:
            // since we and 2 values that both have the most significant byte set to zero
            // the output will always have the most significant byte set to zero
            unsafe { I24::from_bits(bits) }
        }
    }

    impl BitOr = BitOrAssign bitor_assign {
        fn bitor(self, rhs) {
            let bits = self.to_bits() | rhs.to_bits();
            // Safety:
            // since we and 2 values that both have the most significant byte set to zero
            // the output will always have the most significant byte set to zero
            unsafe { I24::from_bits(bits) }
        }
    }

    impl BitXor = BitXorAssign bitxor_assign {
        fn bitxor(self, rhs) {
            let bits = self.to_bits() ^ rhs.to_bits();
            // Safety:
            // since we and 2 values that both have the most significant byte set to zero
            // the output will always have the most significant byte set to zero
            unsafe { I24::from_bits(bits) }
        }
    }
}

impl Hash for I24 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        I24Repr::hash(&self.0, state);
    }

    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
    where
        Self: Sized,
    {
        // I24 is repr(transparent) and compile-time assertions above ensure safety
        I24Repr::hash_slice(
            unsafe { core::mem::transmute::<&[Self], &[I24Repr]>(data) },
            state,
        );
    }
}

macro_rules! impl_from {
    ($($ty: ty : $func_name: ident),+ $(,)?) => {$(
        impl From<$ty> for I24 {
            fn from(value: $ty) -> Self {
                Self::$func_name(value)
            }
        }

        impl I24 {
            #[doc = concat!("Creates an `I24` from a `", stringify!($ty), "` value.")]
            ///
            /// This conversion is guaranteed to succeed as the source type fits within the 24-bit range.
            pub const fn $func_name(value: $ty) -> Self {
                Self(I24Repr::$func_name(value))
            }
        }
    )+};
}

macro_rules! impl_try {
    ($($ty: ty : $func_name: ident),+ $(,)?) => {$(
        impl TryFrom<$ty> for I24 {
            type Error = TryFromIntError;

            fn try_from(value: $ty) -> Result<Self, Self::Error> {
                Self::$func_name(value).ok_or_else(out_of_range)
            }
        }

        impl I24 {
            #[doc = concat!("Tries to create an `I24` from a `", stringify!($ty), "` value.")]
            ///
            /// Returns `Some(I24)` if the value fits within the 24-bit signed range [-8,388,608, 8,388,607],
            /// or `None` if the value is out of range.
            pub const fn $func_name(value: $ty) -> Option<Self> {
                match I24Repr::$func_name(value) {
                    Some(x) => Some(Self(x)),
                    None => None
                }
            }
        }
    )+};
}

impl_from! {
    u8: from_u8,
    u16: from_u16,
    bool: from_bool,

    i8: from_i8,
    i16: from_i16,
}

impl_try! {
    u32 : try_from_u32,
    u64 : try_from_u64,
    u128: try_from_u128,

    i32 : try_from_i32,
    i64 : try_from_i64,
    i128: try_from_i128,
}

// From<I24> for larger integer types (always succeeds)
impl From<I24> for i32 {
    #[inline]
    fn from(value: I24) -> Self {
        value.to_i32()
    }
}

impl From<I24> for i64 {
    #[inline]
    fn from(value: I24) -> Self {
        <Self as From<i32>>::from(value.to_i32())
    }
}

impl From<I24> for i128 {
    #[inline]
    fn from(value: I24) -> Self {
        <Self as From<i32>>::from(value.to_i32())
    }
}

impl From<I24> for isize {
    #[inline]
    fn from(value: I24) -> Self {
        value.to_i32() as Self
    }
}

impl One for I24 {
    fn one() -> Self {
        i24!(1)
    }
}

impl Zero for I24 {
    #[inline]
    fn zero() -> Self {
        Self::zeroed()
    }

    #[inline]
    fn is_zero(&self) -> bool {
        Self::zeroed() == *self
    }
}

pub const fn from_str_error(bad_val: &str) -> ParseIntError {
    match i8::from_str_radix(bad_val, 10) {
        Err(err) => err,
        Ok(_) => unreachable!(),
    }
}

const POSITIVE_OVERFLOW: ParseIntError = from_str_error("9999999999999999999999999999999999999999");

const NEGATIVE_OVERFLOW: ParseIntError =
    from_str_error("-9999999999999999999999999999999999999999");

macro_rules! from_str {
    ($meth: ident($($args: tt)*)) => {
        i32::$meth($($args)*)
            .and_then(|x| I24::try_from_i32(x).ok_or_else(|| {
                if x < 0 {
                    NEGATIVE_OVERFLOW
                } else {
                    POSITIVE_OVERFLOW
                }
            }))
    };
}

impl Num for I24 {
    type FromStrRadixErr = ParseIntError;
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        from_str!(from_str_radix(str, radix))
    }
}

impl FromStr for I24 {
    type Err = ParseIntError;

    fn from_str(str: &str) -> Result<Self, Self::Err> {
        from_str!(from_str(str))
    }
}

impl Neg for I24 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        // this is how you negate two's complement numbers
        Self::from_bits_truncate((!self.to_bits()) + 1)
    }
}

impl Signed for I24 {
    #[inline]
    fn abs(&self) -> Self {
        (*self).abs()
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        (*self).abs_sub(other)
    }

    #[inline]
    fn signum(&self) -> Self {
        (*self).signum()
    }

    #[inline]
    fn is_positive(&self) -> bool {
        (*self).is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        (*self).is_negative()
    }
}

impl Not for I24 {
    type Output = Self;

    #[inline]
    fn not(self) -> Self {
        Self::from_bits_truncate(!self.to_bits())
    }
}

impl Shl<u32> for I24 {
    type Output = Self;

    #[inline]
    fn shl(self, rhs: u32) -> Self::Output {
        // Match Rust's standard behavior: mask shift count to bit width
        let n = rhs % 24;
        Self::from_bits_truncate(self.to_bits() << n)
    }
}

impl Shr<u32> for I24 {
    type Output = Self;

    #[inline]
    fn shr(self, rhs: u32) -> Self::Output {
        // Match Rust's standard behavior: mask shift count to bit width
        let n = rhs % 24;

        // Safety:
        // we do a logical shift right by 8 at the end
        // and so the most significant octet/byte is set to 0

        // logic:
        // <8 bits empty> <I24 sign bit> <rest>
        // we shift everything up by 8
        // <I24 sign bit on i32 sign bit> <rest> <8 bits empty>
        // then we do an arithmetic shift
        // <sign bit * n> <I24 sign bit> <rest> <8 - n bits empty>
        // after we shift everything down by 8
        // <8 bits empty> <sign bit * n> <sign bit> <first 23 - n bits of rest>
        unsafe { Self::from_bits(((self.to_bits() << 8) as i32 >> n) as u32 >> 8) }
    }
}

impl ShrAssign<u32> for I24 {
    #[inline]
    fn shr_assign(&mut self, rhs: u32) {
        *self = Shr::shr(*self, rhs);
    }
}

impl ShlAssign<u32> for I24 {
    #[inline]
    fn shl_assign(&mut self, rhs: u32) {
        *self = Shl::shl(*self, rhs);
    }
}

macro_rules! impl_fmt {
    ($(impl $name: path)+) => {$(
        impl $name for I24 {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <i32 as $name>::fmt(&I24::to_i32(*self), f)
            }
        }
    )*};
}

macro_rules! impl_bits_fmt {
    ($(impl $name: path)+) => {$(
        impl $name for I24 {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <u32 as $name>::fmt(self.as_bits(), f)
            }
        }
    )*};
}

impl_fmt! {
    impl Display
    impl Debug
}

// Custom hex formatting for 24-bit width (6 digits)
impl UpperHex for I24 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:06X}", self.to_bits() & 0x00FF_FFFF)
    }
}

impl LowerHex for I24 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:06x}", self.to_bits() & 0x00FF_FFFF)
    }
}

impl_bits_fmt! {
    impl Octal
    impl fmt::Binary
}

#[cfg(feature = "serde")]
mod serde {
    impl serde::Serialize for crate::I24 {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serializer.serialize_i32(self.to_i32())
        }
    }

    impl<'de> serde::Deserialize<'de> for crate::I24 {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserializer.deserialize_any(I24Visitor)
        }
    }

    struct I24Visitor;

    macro_rules! impl_deserialize_infallible {
        ($([$ty: path, $visit: ident, $from: ident])+) => {$(
            fn $visit<E>(self, v: $ty) -> Result<Self::Value, E> {
                Ok(crate::I24::$from(v))
            }
        )*};
    }

    macro_rules! impl_deserialize_fallible {
        ($([$ty: path, $visit: ident, $try_from: ident])+) => {$(
            fn $visit<E>(self, v: $ty) -> Result<Self::Value, E> where E: serde::de::Error {
                crate::I24::$try_from(v).ok_or_else(|| E::custom("I24 out of range!"))
            }
        )*};
    }

    impl serde::de::Visitor<'_> for I24Visitor {
        type Value = crate::I24;

        fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
            formatter.write_str("an integer between -2^23 and 2^23")
        }

        impl_deserialize_infallible! {
            [u8, visit_u8, from_u8]
            [i8, visit_i8, from_i8]
            [u16, visit_u16, from_u16]
            [i16, visit_i16, from_i16]
        }

        impl_deserialize_fallible! {
            [u32, visit_u32, try_from_u32]
            [i32, visit_i32, try_from_i32]
            [u64, visit_u64, try_from_u64]
            [i64, visit_i64, try_from_i64]
            [u128, visit_u128, try_from_u128]
            [i128, visit_i128, try_from_i128]
        }
    }
}

// Compile-time assertions to ensure transmute safety
const _: () = assert!(core::mem::size_of::<I24>() == core::mem::size_of::<I24Repr>());
const _: () = assert!(core::mem::align_of::<I24>() == core::mem::align_of::<I24Repr>());

impl ToBytes for I24 {
    type Bytes = [u8; 3];

    fn to_be_bytes(&self) -> Self::Bytes {
        self.0.to_be_bytes()
    }

    fn to_le_bytes(&self) -> Self::Bytes {
        self.0.to_le_bytes()
    }
}

impl ToPrimitive for I24 {
    #[inline]
    fn to_i64(&self) -> Option<i64> {
        Some(<i64 as From<i32>>::from(Self::to_i32(*self)))
    }

    #[inline]
    fn to_u64(&self) -> Option<u64> {
        let val = Self::to_i32(*self);
        if val < 0 { None } else { Some(val as u64) }
    }

    #[inline]
    fn to_i32(&self) -> Option<i32> {
        Some(Self::to_i32(*self))
    }

    #[inline]
    fn to_u32(&self) -> Option<u32> {
        let val = Self::to_i32(*self);
        if val < 0 { None } else { Some(val as u32) }
    }

    #[inline]
    fn to_i16(&self) -> Option<i16> {
        let val = Self::to_i32(*self);
        if val < <i32 as From<i16>>::from(i16::MIN) || val > <i32 as From<i16>>::from(i16::MAX) {
            None
        } else {
            Some(val as i16)
        }
    }

    #[inline]
    fn to_u16(&self) -> Option<u16> {
        let val = Self::to_i32(*self);
        if val < 0 || val > <i32 as From<u16>>::from(u16::MAX) {
            None
        } else {
            Some(val as u16)
        }
    }

    #[inline]
    fn to_i8(&self) -> Option<i8> {
        let val = Self::to_i32(*self);
        if val < <i32 as From<i8>>::from(i8::MIN) || val > <i32 as From<i8>>::from(i8::MAX) {
            None
        } else {
            Some(val as i8)
        }
    }

    #[inline]
    fn to_u8(&self) -> Option<u8> {
        let val = Self::to_i32(*self);
        if val < 0 || val > <i32 as From<u8>>::from(u8::MAX) {
            None
        } else {
            Some(val as u8)
        }
    }

    #[inline]
    fn to_isize(&self) -> Option<isize> {
        Some(Self::to_i32(*self) as isize)
    }

    #[inline]
    fn to_usize(&self) -> Option<usize> {
        let val = Self::to_i32(*self);
        if val < 0 { None } else { Some(val as usize) }
    }

    #[inline]
    fn to_f32(&self) -> Option<f32> {
        Some(Self::to_i32(*self) as f32)
    }

    #[inline]
    fn to_f64(&self) -> Option<f64> {
        Some(<f64 as From<i32>>::from(Self::to_i32(*self)))
    }

    #[inline]
    fn to_i128(&self) -> Option<i128> {
        Some(<i128 as From<i32>>::from(Self::to_i32(*self)))
    }

    #[inline]
    fn to_u128(&self) -> Option<u128> {
        let val = Self::to_i32(*self);
        if val < 0 { None } else { Some(val as u128) }
    }
}

/// Implementation of the `NumCast` trait for `I24`.
///
/// This allows safe casting from any type that implements `ToPrimitive`
/// to `I24`. The conversion returns `None` if the source value cannot
/// be represented within the 24-bit signed integer range [-8,388,608, 8,388,607].
#[cfg(feature = "num-cast")]
impl NumCast for I24 {
    /// Converts a value of type `T` to `I24`.
    ///
    /// # Arguments
    ///
    /// * `n` - The value to convert, which must implement `ToPrimitive`.
    ///
    /// # Returns
    ///
    /// * `Some(I24)` if the conversion succeeds and the value is within range.
    /// * `None` if the conversion fails or the value is out of range.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24;
    /// use num_traits::NumCast;
    ///
    /// // Successful conversions
    /// assert_eq!(<I24 as NumCast>::from(1000i32), Some(I24::try_from_i32(1000).unwrap()));
    /// assert_eq!(<I24 as NumCast>::from(500u16), Some(I24::try_from_i32(500).unwrap()));
    ///
    /// // Out of range conversions
    /// assert_eq!(<I24 as NumCast>::from(10_000_000i32), None);
    /// assert_eq!(<I24 as NumCast>::from(-10_000_000i32), None);
    /// ```
    #[inline]
    fn from<T: ToPrimitive>(n: T) -> Option<Self> {
        n.to_i64().and_then(Self::try_from_i64)
    }
}

#[cfg(feature = "ndarray")]
mod ndarray_support {
    impl ndarray::ScalarOperand for crate::I24 {}
    impl ndarray::ScalarOperand for crate::I24Bytes {}
}

#[cfg(feature = "pyo3")]
pub mod python {
    extern crate std;

    use crate::I24;
    use numpy::{Element, PyArrayDescr};
    use pyo3::Py;
    use pyo3::exceptions::PyOverflowError;
    use pyo3::{
        conversion::{FromPyObject, IntoPyObject},
        prelude::*,
        sync::PyOnceLock,
    };

    /// Python wrapper for the `I24` type.
    ///
    /// This struct provides Python bindings for the 24-bit signed integer type,
    /// allowing `I24` values to be used from Python code via `PyO3`.
    #[pyclass(name = "I24", frozen)]
    pub struct PyI24 {
        /// The wrapped `I24` value.
        pub value: I24,
    }

    impl PyI24 {
        /// Creates a new `PyI24` instance from an `I24` value.
        ///
        /// # Arguments
        ///
        /// * `value` - The `I24` value to wrap in the `PyI24` struct.
        ///
        /// # Returns
        ///
        /// A new `PyI24` instance containing the provided `I24` value.
        #[must_use]
        pub const fn new(value: I24) -> Self {
            Self { value }
        }
    }

    #[pymethods]
    impl PyI24 {
        #[new]
        #[pyo3(signature = (value: "int"), text_signature = "(value: int) -> None")]
        fn py_new(value: i32) -> PyResult<Self> {
            I24::try_from_i32(value).map_or_else(
                || {
                    Err(pyo3::exceptions::PyValueError::new_err(
                        "value must be between -8388608 and 8388607",
                    ))
                },
                |i24| Ok(Self { value: i24 }),
            )
        }

        #[staticmethod]
        #[pyo3(signature = (bytes: "list[int]", byteorder: "Literal['little', 'big', 'native']" = "native"), text_signature = "(bytes: list[int], byteorder: Literal['little', 'big', 'native']) -> Self")]
        fn from_bytes(bytes: &[u8], byteorder: Option<&str>) -> PyResult<Self> {
            if bytes.len() != 3 {
                return Err(pyo3::exceptions::PyValueError::new_err(
                    "bytes must be exactly 3 bytes long",
                ));
            }
            let byte_array: [u8; 3] = [bytes[0], bytes[1], bytes[2]];
            let byteorder = byteorder.unwrap_or("native");
            let value = match byteorder {
                "little" => I24::from_le_bytes(byte_array),
                "big" => I24::from_be_bytes(byte_array),
                "native" => I24::from_ne_bytes(byte_array),
                _ => {
                    return Err(pyo3::exceptions::PyValueError::new_err(
                        "byteorder must be 'little', 'big', or 'native'",
                    ));
                }
            };
            Ok(Self { value })
        }

        #[pyo3(signature = (), text_signature = "($self) -> int")]
        const fn to_int(&self) -> i32 {
            self.value.to_i32()
        }

        #[pyo3(signature = (byteorder: "Literal['little', 'big', 'native']" = "native"), text_signature = "($self, byteorder: Literal['little', 'big', 'native']) -> list[int]")]
        fn to_bytes(&self, byteorder: &str) -> PyResult<Vec<u8>> {
            let bytes = match byteorder {
                "little" => self.value.to_le_bytes(),
                "big" => self.value.to_be_bytes(),
                "native" => self.value.to_ne_bytes(),
                _ => {
                    return Err(pyo3::exceptions::PyValueError::new_err(
                        "byteorder must be 'little', 'big', or 'native'",
                    ));
                }
            };
            Ok(bytes.to_vec())
        }

        fn __str__(&self) -> String {
            format!("{}", self.value.to_i32())
        }

        fn __repr__(&self) -> String {
            format!("I24({})", self.value.to_i32())
        }

        const fn __int__(&self) -> i32 {
            self.value.to_i32()
        }

        // Comparison operators
        fn __eq__(&self, other: &Self) -> bool {
            self.value == other.value
        }

        fn __ne__(&self, other: &Self) -> bool {
            self.value != other.value
        }

        fn __lt__(&self, other: &Self) -> bool {
            self.value < other.value
        }

        fn __le__(&self, other: &Self) -> bool {
            self.value <= other.value
        }

        fn __gt__(&self, other: &Self) -> bool {
            self.value > other.value
        }

        fn __ge__(&self, other: &Self) -> bool {
            self.value >= other.value
        }

        // Cross-type comparisons with Python int
        const fn __eq_int__(&self, other: i32) -> bool {
            self.value.to_i32() == other
        }

        const fn __ne_int__(&self, other: i32) -> bool {
            self.value.to_i32() != other
        }

        const fn __lt_int__(&self, other: i32) -> bool {
            self.value.to_i32() < other
        }

        const fn __le_int__(&self, other: i32) -> bool {
            self.value.to_i32() <= other
        }

        const fn __gt_int__(&self, other: i32) -> bool {
            self.value.to_i32() > other
        }

        const fn __ge_int__(&self, other: i32) -> bool {
            self.value.to_i32() >= other
        }

        // Arithmetic operators
        fn __add__(&self, other: &Self) -> PyResult<Self> {
            self.value.checked_add(other.value).map_or_else(
                || Err(PyOverflowError::new_err("I24 addition overflow")),
                |result| Ok(Self { value: result }),
            )
        }

        fn __sub__(&self, other: &Self) -> PyResult<Self> {
            self.value.checked_sub(other.value).map_or_else(
                || Err(PyOverflowError::new_err("I24 subtraction overflow")),
                |result| Ok(Self { value: result }),
            )
        }

        fn __mul__(&self, other: &Self) -> PyResult<Self> {
            self.value.checked_mul(other.value).map_or_else(
                || Err(PyOverflowError::new_err("I24 multiplication overflow")),
                |result| Ok(Self { value: result }),
            )
        }

        fn __truediv__(&self, other: &Self) -> PyResult<f64> {
            if other.value.to_i32() == 0 {
                return Err(pyo3::exceptions::PyZeroDivisionError::new_err(
                    "division by zero",
                ));
            }
            Ok(f64::from(self.value.to_i32()) / f64::from(other.value.to_i32()))
        }

        fn __floordiv__(&self, other: &Self) -> PyResult<Self> {
            self.value.checked_div(other.value).map_or_else(
                || {
                    Err(pyo3::exceptions::PyZeroDivisionError::new_err(
                        "division by zero",
                    ))
                },
                |result| Ok(Self { value: result }),
            )
        }

        fn __mod__(&self, other: &Self) -> PyResult<Self> {
            self.value.checked_rem(other.value).map_or_else(
                || {
                    Err(pyo3::exceptions::PyZeroDivisionError::new_err(
                        "division by zero",
                    ))
                },
                |result| Ok(Self { value: result }),
            )
        }

        // Bitwise operations
        fn __and__(&self, other: &Self) -> Self {
            Self {
                value: self.value & other.value,
            }
        }

        fn __or__(&self, other: &Self) -> Self {
            Self {
                value: self.value | other.value,
            }
        }

        fn __xor__(&self, other: &Self) -> Self {
            Self {
                value: self.value ^ other.value,
            }
        }

        fn __lshift__(&self, other: u32) -> PyResult<Self> {
            if other >= 32 {
                return Err(pyo3::exceptions::PyValueError::new_err(
                    "shift count out of range",
                ));
            }
            let result = (self.value.to_i32() as u32) << other;
            I24::try_from_i32(result as i32).map_or_else(
                || Err(PyOverflowError::new_err("I24 left shift overflow")),
                |val| Ok(Self { value: val }),
            )
        }

        fn __rshift__(&self, other: u32) -> PyResult<Self> {
            if other >= 32 {
                return Err(pyo3::exceptions::PyValueError::new_err(
                    "shift count out of range",
                ));
            }
            let result = self.value.to_i32() >> other;
            Ok(Self {
                value: I24::wrapping_from_i32(result),
            })
        }

        // Utility methods
        #[classattr]
        const fn min_value() -> Self {
            Self { value: I24::MIN }
        }

        #[classattr]
        const fn max_value() -> Self {
            Self { value: I24::MAX }
        }

        #[pyo3(signature = (), text_signature = "($self) -> int")]
        const fn count_ones(&self) -> u32 {
            self.value.to_i32().count_ones()
        }

        #[pyo3(signature = (), text_signature = "($self) -> int")]
        const fn count_zeros(&self) -> u32 {
            self.value.to_i32().count_zeros()
        }

        #[pyo3(signature = (), text_signature = "($self) -> int")]
        const fn leading_zeros(&self) -> u32 {
            self.value.to_i32().leading_zeros()
        }

        #[pyo3(signature = (), text_signature = "($self) -> int")]
        const fn trailing_zeros(&self) -> u32 {
            self.value.to_i32().trailing_zeros()
        }

        // Checked methods
        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        fn checked_add(&self, other: &Self) -> Option<Self> {
            self.value
                .checked_add(other.value)
                .map(|v| Self { value: v })
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        fn checked_sub(&self, other: &Self) -> Option<Self> {
            self.value
                .checked_sub(other.value)
                .map(|v| Self { value: v })
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        fn checked_mul(&self, other: &Self) -> Option<Self> {
            self.value
                .checked_mul(other.value)
                .map(|v| Self { value: v })
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        fn checked_div(&self, other: &Self) -> Option<Self> {
            self.value
                .checked_div(other.value)
                .map(|v| Self { value: v })
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        const fn wrapping_add(&self, other: &Self) -> Self {
            let result = self.value.to_i32().wrapping_add(other.value.to_i32());
            Self {
                value: I24::wrapping_from_i32(result),
            }
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        const fn wrapping_sub(&self, other: &Self) -> Self {
            let result = self.value.to_i32().wrapping_sub(other.value.to_i32());
            Self {
                value: I24::wrapping_from_i32(result),
            }
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        const fn wrapping_mul(&self, other: &Self) -> Self {
            let result = self.value.to_i32().wrapping_mul(other.value.to_i32());
            Self {
                value: I24::wrapping_from_i32(result),
            }
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        const fn saturating_add(&self, other: &Self) -> Self {
            let result = self.value.to_i32().saturating_add(other.value.to_i32());
            Self {
                value: I24::saturating_from_i32(result),
            }
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        const fn saturating_sub(&self, other: &Self) -> Self {
            let result = self.value.to_i32().saturating_sub(other.value.to_i32());
            Self {
                value: I24::saturating_from_i32(result),
            }
        }

        #[pyo3(signature = (other: "I24"), text_signature = "($self, other: I24) -> Optional[I24]")]
        const fn saturating_mul(&self, other: &Self) -> Self {
            let result = self.value.to_i32().saturating_mul(other.value.to_i32());
            Self {
                value: I24::saturating_from_i32(result),
            }
        }

        // Additional Python magic methods
        fn __hash__(&self) -> u64 {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let mut hasher = DefaultHasher::new();
            self.value.hash(&mut hasher);
            hasher.finish()
        }

        fn __abs__(&self) -> PyResult<Self> {
            let abs_val = self.value.to_i32().abs();

            I24::try_from_i32(abs_val).map_or_else(
                || {
                    Err(PyOverflowError::new_err(
                        "Absolute value overflow for I24::MIN",
                    ))
                },
                |v| Ok(Self { value: v }),
            )
        }

        fn __neg__(&self) -> PyResult<Self> {
            self.value.checked_neg().map_or_else(
                || {
                    Err(PyOverflowError::new_err(
                        "I24 negation overflow for I24::MIN",
                    ))
                },
                |result| Ok(Self { value: result }),
            )
        }

        const fn __pos__(&self) -> Self {
            Self { value: self.value }
        }

        fn __invert__(&self) -> Self {
            let inverted = !self.value;
            Self { value: inverted }
        }

        // Pythonic method names
        #[pyo3(signature = (), text_signature = "($self) -> int")]
        const fn bit_length(&self) -> u32 {
            let val = if self.value.to_i32() < 0 {
                (!self.value.to_i32()) as u32
            } else {
                self.value.to_i32() as u32
            };
            32 - val.leading_zeros()
        }

        #[pyo3(signature = (), text_signature = "($self) -> int")]
        const fn bit_count(&self) -> u32 {
            let abs_val = self.value.to_i32().unsigned_abs();
            abs_val.count_ones()
        }

        #[pyo3(signature = (), text_signature = "($self) -> Tuple[int, int]")]
        const fn as_integer_ratio(&self) -> (i32, i32) {
            (self.value.to_i32(), 1)
        }

        const fn __ceil__(&self) -> Self {
            Self { value: self.value }
        }

        const fn __floor__(&self) -> Self {
            Self { value: self.value }
        }

        const fn __trunc__(&self) -> Self {
            Self { value: self.value }
        }
    }

    unsafe impl Element for I24 {
        const IS_COPY: bool = true;

        fn clone_ref(&self, _py: Python<'_>) -> Self {
            *self
        }

        fn get_dtype(py: Python<'_>) -> Bound<'_, PyArrayDescr> {
            // IMPORTANT: do not call `numpy::dtype::<I24>` here; that dispatches to
            // `I24::get_dtype` and will recurse.
            //
            // NumPy has no native 24-bit integer dtype, and `I24` is represented in-memory
            // as a 4-byte value with the top byte always zero. We therefore expose it as an
            // opaque 4-byte dtype.
            static DTYPE: PyOnceLock<Py<PyArrayDescr>> = PyOnceLock::new();

            DTYPE
                .get_or_init(py, || {
                    PyArrayDescr::new(py, "V4")
                        .expect("Failed to construct NumPy dtype for I24")
                        .unbind()
                })
                .clone_ref(py)
                .into_bound(py)
        }
    }

    // IntoPyObject implementation for I24 - converts to Python int
    impl<'py> IntoPyObject<'py> for I24 {
        type Target = pyo3::types::PyInt;
        type Output = Bound<'py, pyo3::types::PyInt>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(self.to_i32().into_pyobject(py)?)
        }
    }

    impl<'py> IntoPyObject<'py> for &I24 {
        type Target = pyo3::types::PyInt;
        type Output = Bound<'py, pyo3::types::PyInt>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(self.to_i32().into_pyobject(py)?)
        }
    }

    // FromPyObject implementation for I24 - converts from Python int
    impl<'a, 'py> FromPyObject<'a, 'py> for I24 {
        type Error = pyo3::PyErr;

        fn extract(obj: pyo3::Borrowed<'a, 'py, pyo3::PyAny>) -> PyResult<Self> {
            let py_int: i32 = obj.extract()?;
            Self::try_from_i32(py_int).ok_or_else(|| {
                pyo3::exceptions::PyOverflowError::new_err(format!(
                    "Value {py_int} is out of range for I24 (-8388608 to 8388607)"
                ))
            })
        }
    }
}

/// Public 3-byte wire representation of a signed 24-bit integer.
///
/// This type represents the exact on-wire format of an `I24` value as 3 consecutive bytes.
/// Unlike the runtime `I24` type which is 4-byte aligned, `I24Bytes` is exactly 3 bytes
/// and can be safely used in packed structs for binary deserialization.
///
/// # Safety for Mixed Packed Structs
///
/// `I24Bytes` is designed to solve the problem of mixed packed structs containing both
/// standard types (like `u32`) and 24-bit integers. Since `bytemuck::Pod` forbids
/// packed structs with native integer fields, you should use byte-oriented types
/// like `I24Bytes` in your wire structs, then convert to native types.
///
/// # Examples
///
/// ```
/// use i24::I24Bytes;
///
/// // Convert from I24 to wire format
/// let value = i24::I24::try_from(123456).expect("Test value should convert successfully");
/// let wire_bytes = I24Bytes::from_i24_le(value);
///
/// // Convert back to I24
/// let recovered = wire_bytes.to_i24_le();
/// assert_eq!(value, recovered);
/// ```
///
/// For use in mixed packed structs, see the examples directory for complete patterns.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[cfg_attr(
    feature = "zerocopy",
    derive(zerocopy::FromBytes, zerocopy::Unaligned, zerocopy::IntoBytes)
)]
pub struct I24Bytes(pub [u8; 3]);

// Safety: I24Bytes is transparent over [u8; 3], which is always valid for any bit pattern
unsafe impl Pod for I24Bytes {}

// Safety: I24Bytes can be safely zero-initialized
unsafe impl Zeroable for I24Bytes {}

impl I24Bytes {
    /// Converts this wire representation to an `I24` value, interpreting bytes as little-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let wire = I24Bytes([0x40, 0xE2, 0x01]); // 123456 in little-endian
    /// let value = wire.to_i24_le();
    /// assert_eq!(value, i24::I24::try_from(123456).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub const fn to_i24_le(self) -> I24 {
        I24::from_le_bytes(self.0)
    }

    /// Converts this wire representation to an `I24` value, interpreting bytes as big-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let wire = I24Bytes([0x01, 0xE2, 0x40]); // 123456 in big-endian
    /// let value = wire.to_i24_be();
    /// assert_eq!(value, i24::I24::try_from(123456).expect("Test value should convert successfully"));
    /// ```
    #[inline]
    #[must_use]
    pub const fn to_i24_be(self) -> I24 {
        I24::from_be_bytes(self.0)
    }

    /// Converts this wire representation to an `I24` value, interpreting bytes as native-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let original = i24::I24::try_from(123456).expect("Test value should convert successfully");
    /// let wire = I24Bytes::from_i24_ne(original);
    /// let value = wire.to_i24_ne();
    /// assert_eq!(value, original);
    /// ```
    #[inline]
    #[must_use]
    pub const fn to_i24_ne(self) -> I24 {
        I24::from_ne_bytes(self.0)
    }

    /// Creates a wire representation from an `I24` value in little-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let value = i24::I24::try_from(123456).expect("Test value should convert successfully");
    /// let wire = I24Bytes::from_i24_le(value);
    /// assert_eq!(wire.0, [0x40, 0xE2, 0x01]); // little-endian bytes
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_i24_le(value: I24) -> Self {
        Self(value.to_le_bytes())
    }

    /// Creates a wire representation from an `I24` value in big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let value = i24::I24::try_from(123456).expect("Test value should convert successfully");
    /// let wire = I24Bytes::from_i24_be(value);
    /// assert_eq!(wire.0, [0x01, 0xE2, 0x40]); // big-endian bytes
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_i24_be(value: I24) -> Self {
        Self(value.to_be_bytes())
    }

    /// Creates a wire representation from an `I24` value in native-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let value = i24::I24::try_from(123456).expect("Test value should convert successfully");
    /// let wire = I24Bytes::from_i24_ne(value);
    /// // Byte order depends on target architecture endianness
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_i24_ne(value: I24) -> Self {
        Self(value.to_ne_bytes())
    }

    /// Creates a wire representation directly from a 3-byte array.
    ///
    /// The byte order interpretation is deferred until conversion with
    /// `to_i24_le()` or `to_i24_be()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let wire = I24Bytes::from_bytes([0x40, 0xE2, 0x01]);
    /// assert_eq!(wire.0, [0x40, 0xE2, 0x01]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_bytes(bytes: [u8; 3]) -> Self {
        Self(bytes)
    }

    /// Returns the raw byte array of this wire representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::I24Bytes;
    ///
    /// let wire = I24Bytes([0x40, 0xE2, 0x01]);
    /// assert_eq!(wire.to_bytes(), [0x40, 0xE2, 0x01]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn to_bytes(self) -> [u8; 3] {
        self.0
    }
}

// Additional trait implementations for I24Bytes
impl AsRef<[u8; 3]> for I24Bytes {
    #[inline]
    fn as_ref(&self) -> &[u8; 3] {
        &self.0
    }
}

impl AsMut<[u8; 3]> for I24Bytes {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8; 3] {
        &mut self.0
    }
}

impl AsRef<[u8]> for I24Bytes {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0[..]
    }
}

impl AsMut<[u8]> for I24Bytes {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0[..]
    }
}

impl From<[u8; 3]> for I24Bytes {
    #[inline]
    fn from(bytes: [u8; 3]) -> Self {
        Self(bytes)
    }
}

impl From<I24Bytes> for [u8; 3] {
    #[inline]
    fn from(i24_bytes: I24Bytes) -> Self {
        i24_bytes.0
    }
}

impl core::ops::Deref for I24Bytes {
    type Target = [u8; 3];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl core::ops::DerefMut for I24Bytes {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// PyO3 implementations for I24Bytes
#[cfg(feature = "pyo3")]
mod i24_bytes_pyo3 {
    use super::I24Bytes;
    use pyo3::{
        conversion::{FromPyObject, IntoPyObject},
        prelude::*,
    };

    // IntoPyObject implementation for I24Bytes - converts to Python bytes
    impl<'py> IntoPyObject<'py> for I24Bytes {
        type Target = pyo3::types::PyBytes;
        type Output = Bound<'py, pyo3::types::PyBytes>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(pyo3::types::PyBytes::new(py, &self.0))
        }
    }

    impl<'py> IntoPyObject<'py> for &I24Bytes {
        type Target = pyo3::types::PyBytes;
        type Output = Bound<'py, pyo3::types::PyBytes>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(pyo3::types::PyBytes::new(py, &self.0))
        }
    }

    // FromPyObject implementation for I24Bytes - converts from Python bytes
    impl<'a, 'py> FromPyObject<'a, 'py> for I24Bytes {
        type Error = pyo3::PyErr;

        fn extract(obj: pyo3::Borrowed<'a, 'py, pyo3::PyAny>) -> PyResult<Self> {
            let py_bytes: &[u8] = obj.extract()?;
            if py_bytes.len() != 3 {
                return Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "Expected exactly 3 bytes for I24Bytes, got {}",
                    py_bytes.len()
                )));
            }
            Ok(Self([py_bytes[0], py_bytes[1], py_bytes[2]]))
        }
    }
}

#[cfg(test)]
mod i24_tests {
    extern crate std;

    use super::*;
    use std::format;
    use std::num::IntErrorKind;

    #[test]
    fn test_arithmetic_operations() {
        let a = i24!(100);
        let b = i24!(50);

        assert_eq!(a + b, i24!(150));
        assert_eq!(a - b, i24!(50));
        assert_eq!(a * b, i24!(5000));
        assert_eq!(a / b, i24!(2));
        assert_eq!(a % b, i24!(0));
    }

    #[test]
    fn test_negative_operations() {
        let a = i24!(100);
        let b = i24!(-50);

        assert_eq!(a + b, i24!(50));
        assert_eq!(a - b, i24!(150));
        assert_eq!(a * b, i24!(-5000));
        assert_eq!(a / b, i24!(-2));
    }

    #[test]
    fn test_bitwise_operations() {
        let a = i24!(0b101010);
        let b = i24!(0b110011);

        assert_eq!(a & b, i24!(0b100010));
        assert_eq!(a | b, i24!(0b111011));
        assert_eq!(a ^ b, i24!(0b011001));
        assert_eq!(a << 2, i24!(0b10101000));
        assert_eq!(a >> 2, i24!(0b1010));
    }

    #[test]
    fn test_checked_addition() {
        assert_eq!(i24!(10).checked_add(i24!(20)), Some(i24!(30)));
        assert_eq!(i24!(10).checked_add(i24!(-20)), Some(i24!(-10)));
        // Overflow cases
        assert_eq!(I24::MAX.checked_add(I24::one()), None);
        assert_eq!(
            (I24::MAX - I24::one()).checked_add(I24::one() * i24!(2)),
            None
        );
    }

    #[test]
    fn test_checked_subtraction() {
        assert_eq!(i24!(10).checked_sub(i24!(20)), Some(i24!(-10)));
        assert_eq!(i24!(10).checked_sub(i24!(-20)), Some(i24!(30)));

        // Overflow cases
        assert_eq!(I24::MIN.checked_sub(I24::one()), None);
        assert_eq!(
            (I24::MIN + I24::one()).checked_sub(I24::one() * i24!(2)),
            None
        );
    }

    #[test]
    fn test_checked_division() {
        assert_eq!(i24!(20).checked_div(i24!(5)), Some(i24!(4)));
        assert_eq!(i24!(20).checked_div(i24!(0)), None);
    }

    #[test]
    fn test_checked_multiplication() {
        assert_eq!(i24!(5).checked_mul(i24!(6)), Some(i24!(30)));
        assert_eq!(I24::MAX.checked_mul(i24!(2)), None);
    }

    #[test]
    fn test_checked_remainder() {
        assert_eq!(i24!(20).checked_rem(i24!(5)), Some(i24!(0)));
        assert_eq!(i24!(20).checked_rem(i24!(0)), None);
    }

    #[test]
    fn test_unary_operations() {
        let a = i24!(100);

        assert_eq!(-a, i24!(-100));
        assert_eq!(!a, i24!(-101));
    }

    #[test]
    fn test_from_bytes() {
        let le = i24!(0x030201);
        let be = i24!(0x010203);
        assert_eq!(
            I24::from_ne_bytes([0x01, 0x02, 0x03]),
            if cfg!(target_endian = "big") { be } else { le }
        );
        assert_eq!(I24::from_le_bytes([0x01, 0x02, 0x03]), le);
        assert_eq!(I24::from_be_bytes([0x01, 0x02, 0x03]), be);
    }

    #[test]
    fn test_zero_and_one() {
        assert_eq!(
            I24::zero(),
            I24::try_from_i32(0).expect("Zero should convert successfully")
        );

        assert_eq!(I24::zero(), i24!(0));
        assert_eq!(I24::one(), i24!(1));
    }

    #[test]
    fn test_from_str() {
        assert_eq!(
            I24::from_str("100").expect("100 should parse successfully"),
            i24!(100)
        );
        assert_eq!(
            I24::from_str("-100").expect("-100 should parse successfully"),
            i24!(-100)
        );
        assert_eq!(
            I24::from_str(&format!("{}", I24::MAX)).expect("MAX should parse successfully"),
            I24::MAX
        );
        assert_eq!(
            I24::from_str(&format!("{}", I24::MIN)).expect("MIN should parse successfully"),
            I24::MIN
        );
        assert_eq!(
            *I24::from_str("8388608")
                .expect_err("Expected parse error")
                .kind(),
            IntErrorKind::PosOverflow
        );
        assert_eq!(
            *I24::from_str("-8388609")
                .expect_err("Expected parse error")
                .kind(),
            IntErrorKind::NegOverflow
        );
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", i24!(100)), "100");
        assert_eq!(format!("{}", i24!(-100)), "-100");
    }

    #[test]
    fn test_wrapping_behavior() {
        assert_eq!(I24::MAX + I24::one(), I24::MIN);
        assert_eq!(I24::MAX + I24::one() + I24::one(), I24::MIN + I24::one());

        assert_eq!(I24::MIN - I24::one(), I24::MAX);
        assert_eq!(I24::MIN - (I24::one() + I24::one()), I24::MAX - I24::one());

        assert_eq!(-I24::MIN, I24::MIN)
    }

    #[test]
    fn discriminant_optimization() {
        // this isn't guaranteed by rustc, but this should still hold true
        // if this fails because rustc stops doing it, just remove this test
        // otherwise investigate why this isn't working
        assert_eq!(size_of::<I24>(), size_of::<Option<I24>>());
        assert_eq!(size_of::<I24>(), size_of::<Option<Option<I24>>>());
        assert_eq!(size_of::<I24>(), size_of::<Option<Option<Option<I24>>>>());
        assert_eq!(
            size_of::<I24>(),
            size_of::<Option<Option<Option<Option<I24>>>>>()
        );
    }

    #[test]
    fn test_shift_operations() {
        let a = i24!(0b1);

        // Left shift
        assert_eq!(a << 23, I24::MIN); // 0x800000, which is the minimum negative value
        assert_eq!(a << 24, a); // Wraps around (same as << 0)

        // Right shift
        let b = i24!(-1); // All bits set
        assert_eq!(b >> 1, i24!(-1)); // Sign extension
        assert_eq!(b >> 23, i24!(-1)); // Still all bits set due to sign extension
        assert_eq!(b >> 24, i24!(-1)); // No change after 23 bits

        // Edge case: maximum positive value
        let c = i24!(0x7FFFFF); // 8388607
        assert_eq!(c << 1, i24!(-2)); // 0xFFFFFE in 24-bit, which is -2 when sign-extended

        // Edge case: minimum negative value
        let d = I24::MIN; // (-0x800000)
        assert_eq!(d >> 1, i24!(-0x400000));
        assert_eq!(d >> 2, i24!(-0x200000));
        assert_eq!(d >> 3, i24!(-0x100000));
        assert_eq!(d >> 4, i24!(-0x080000));

        // Additional test for left shift wrapping
        assert_eq!(c << 1, i24!(-2)); // 0xFFFFFE
        assert_eq!(c << 2, i24!(-4)); // 0xFFFFFC
        assert_eq!(c << 3, i24!(-8)); // 0xFFFFF8
    }

    #[test]
    fn test_to_from_i32() {
        for i in I24Repr::MIN..=I24Repr::MAX {
            assert_eq!(
                I24::try_from_i32(i)
                    .expect("Value in range should convert successfully")
                    .to_i32(),
                i
            )
        }
    }

    #[test]
    fn test_from() {
        macro_rules! impl_t {
            ($($ty: ty),+) => {{$(
                for x in <$ty>::MIN..=<$ty>::MAX {
                    assert_eq!(<$ty>::try_from(<I24 as From<$ty>>::from(x).to_i32()).expect("Value should convert back"), x)
                }
            )+}};
        }

        assert_eq!(<I24 as From<bool>>::from(true), I24::one());
        assert_eq!(<I24 as From<bool>>::from(false), I24::zero());

        impl_t!(i8, i16, u8, u16)
    }

    #[test]
    fn test_try_from() {
        macro_rules! impl_t {
            (signed $($ty: ty),+) => {{$(
                for x in I24Repr::MIN..=I24Repr::MAX {
                    assert_eq!(I24::try_from(<$ty as From<i32>>::from(x)).expect("Value should convert successfully").to_i32(), x)
                }
            )+}};

            (unsigned $($ty: ty),+) => {{$(
                for x in 0..=I24Repr::MAX {
                    assert_eq!(I24::try_from(<$ty>::try_from(x).expect("Value should fit in type")).expect("Value should convert to I24").to_i32(), x)
                }
            )+}};
        }

        impl_t!(signed i32, i64, i128);
        impl_t!(unsigned u32, u64, u128);
    }

    #[test]
    fn test_to_from_bits() {
        for i in 0..(1 << 24) {
            assert_eq!(I24::from_bits_truncate(i).to_bits(), i)
        }
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_deserialize_json() {
        #[derive(Debug, PartialEq, ::serde::Deserialize)]
        struct TestStruct {
            value: I24,
        }

        let test: TestStruct =
            serde_json::from_str("{ \"value\": 11 }").expect("Failed to deserialize!");
        let expected = TestStruct {
            value: I24::from_u8(11),
        };

        assert_eq!(test, expected);
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_serialize_json() {
        #[derive(Debug, PartialEq, ::serde::Serialize)]
        struct TestStruct {
            value: I24,
        }

        let test_struct = TestStruct {
            value: I24::from_u8(11),
        };
        let test = serde_json::to_string(&test_struct).expect("Failed to serialize!");
        assert_eq!(test, "{\"value\":11}");
    }

    #[test]
    fn test_to_primitive_signed() {
        use num_traits::ToPrimitive;

        // Test positive values
        let val = i24!(100);
        assert_eq!(val.to_i8(), Some(100i8));
        assert_eq!(val.to_i16(), Some(100i16));
        assert_eq!(ToPrimitive::to_i32(&val), Some(100i32));
        assert_eq!(val.to_i64(), Some(100i64));
        assert_eq!(val.to_i128(), Some(100i128));
        assert_eq!(val.to_isize(), Some(100isize));

        // Test negative values
        let val = i24!(-100);
        assert_eq!(val.to_i8(), Some(-100i8));
        assert_eq!(val.to_i16(), Some(-100i16));
        assert_eq!(ToPrimitive::to_i32(&val), Some(-100i32));
        assert_eq!(val.to_i64(), Some(-100i64));
        assert_eq!(val.to_i128(), Some(-100i128));
        assert_eq!(val.to_isize(), Some(-100isize));

        // Test overflow cases for smaller types
        let val = I24::MAX;
        assert_eq!(val.to_i8(), None); // I24::MAX > i8::MAX
        assert_eq!(val.to_i16(), None); // I24::MAX > i16::MAX
        assert_eq!(ToPrimitive::to_i32(&val), Some(I24::MAX.to_i32()));

        let val = I24::MIN;
        assert_eq!(val.to_i8(), None); // I24::MIN < i8::MIN
        assert_eq!(val.to_i16(), None); // I24::MIN < i16::MIN
        assert_eq!(ToPrimitive::to_i32(&val), Some(I24::MIN.to_i32()));
    }

    #[test]
    fn test_to_primitive_unsigned() {
        use num_traits::ToPrimitive;

        // Test positive values
        let val = i24!(100);
        assert_eq!(val.to_u8(), Some(100u8));
        assert_eq!(val.to_u16(), Some(100u16));
        assert_eq!(val.to_u32(), Some(100u32));
        assert_eq!(val.to_u64(), Some(100u64));
        assert_eq!(val.to_u128(), Some(100u128));
        assert_eq!(val.to_usize(), Some(100usize));

        // Test negative values should return None for unsigned types
        let val = i24!(-100);
        assert_eq!(val.to_u8(), None);
        assert_eq!(val.to_u16(), None);
        assert_eq!(val.to_u32(), None);
        assert_eq!(val.to_u64(), None);
        assert_eq!(val.to_u128(), None);
        assert_eq!(val.to_usize(), None);

        // Test overflow cases for smaller unsigned types
        let val = I24::MAX;
        assert_eq!(val.to_u8(), None); // I24::MAX > u8::MAX
        assert_eq!(val.to_u16(), None); // I24::MAX > u16::MAX
        assert_eq!(val.to_u32(), Some(I24::MAX.to_i32() as u32));

        // Test zero
        let val = i24!(0);
        assert_eq!(val.to_u8(), Some(0u8));
        assert_eq!(val.to_u16(), Some(0u16));
        assert_eq!(val.to_u32(), Some(0u32));
        assert_eq!(val.to_u64(), Some(0u64));
        assert_eq!(val.to_u128(), Some(0u128));
        assert_eq!(val.to_usize(), Some(0usize));
    }

    #[test]
    fn test_to_primitive_floats() {
        use num_traits::ToPrimitive;

        // Test positive values
        let val = i24!(100);
        assert_eq!(val.to_f32(), Some(100.0f32));
        assert_eq!(val.to_f64(), Some(100.0f64));

        // Test negative values
        let val = i24!(-100);
        assert_eq!(val.to_f32(), Some(-100.0f32));
        assert_eq!(val.to_f64(), Some(-100.0f64));

        // Test extreme values
        let val = I24::MAX;
        assert_eq!(val.to_f32(), Some(I24::MAX.to_i32() as f32));
        assert_eq!(val.to_f64(), Some(I24::MAX.to_i32() as f64));

        let val = I24::MIN;
        assert_eq!(val.to_f32(), Some(I24::MIN.to_i32() as f32));
        assert_eq!(val.to_f64(), Some(I24::MIN.to_i32() as f64));
    }

    #[test]
    fn test_to_primitive_boundary_values() {
        use num_traits::ToPrimitive;

        // Test values at the boundaries of smaller types
        let val = i24!(127); // i8::MAX
        assert_eq!(val.to_i8(), Some(127i8));
        assert_eq!(val.to_u8(), Some(127u8));

        let val = i24!(128); // i8::MAX + 1
        assert_eq!(val.to_i8(), None);
        assert_eq!(val.to_u8(), Some(128u8));

        let val = i24!(255); // u8::MAX
        assert_eq!(val.to_u8(), Some(255u8));

        let val = i24!(256); // u8::MAX + 1
        assert_eq!(val.to_u8(), None);

        let val = i24!(32767); // i16::MAX
        assert_eq!(val.to_i16(), Some(32767i16));
        assert_eq!(val.to_u16(), Some(32767u16));

        let val = i24!(32768); // i16::MAX + 1
        assert_eq!(val.to_i16(), None);
        assert_eq!(val.to_u16(), Some(32768u16));

        let val = i24!(65535); // u16::MAX
        assert_eq!(val.to_u16(), Some(65535u16));

        let val = i24!(65536); // u16::MAX + 1
        assert_eq!(val.to_u16(), None);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_packed_struct_utilities() {
        use crate::PackedStruct;
        use alloc::vec;
        use alloc::vec::Vec;

        // Define a test structure similar to the issue example
        #[derive(Debug, Clone, PartialEq)]
        struct TestDataStruct {
            t: u32,
            ch1: I24,
            ch2: I24,
            ch3: I24,
            ch4: I24,
            s: I24,
        }

        impl PackedStruct for TestDataStruct {
            const PACKED_SIZE: usize = 4 + 5 * 3; // u32 + 5 * I24 = 19 bytes

            fn from_packed_bytes(bytes: &[u8]) -> Option<Self> {
                if bytes.len() < Self::PACKED_SIZE {
                    return None;
                }

                let t = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                let ch1 = I24::from_le_bytes([bytes[4], bytes[5], bytes[6]]);
                let ch2 = I24::from_le_bytes([bytes[7], bytes[8], bytes[9]]);
                let ch3 = I24::from_le_bytes([bytes[10], bytes[11], bytes[12]]);
                let ch4 = I24::from_le_bytes([bytes[13], bytes[14], bytes[15]]);
                let s = I24::from_le_bytes([bytes[16], bytes[17], bytes[18]]);

                Some(TestDataStruct {
                    t,
                    ch1,
                    ch2,
                    ch3,
                    ch4,
                    s,
                })
            }

            fn to_packed_bytes(&self) -> Vec<u8> {
                let mut bytes = Vec::with_capacity(Self::PACKED_SIZE);
                bytes.extend_from_slice(&self.t.to_le_bytes());
                bytes.extend_from_slice(&self.ch1.to_le_bytes());
                bytes.extend_from_slice(&self.ch2.to_le_bytes());
                bytes.extend_from_slice(&self.ch3.to_le_bytes());
                bytes.extend_from_slice(&self.ch4.to_le_bytes());
                bytes.extend_from_slice(&self.s.to_le_bytes());
                bytes
            }
        }

        // Test data
        let original = TestDataStruct {
            t: 0x12345678,
            ch1: I24::try_from_i32(0x123456).expect("Test value should convert successfully"),
            ch2: I24::try_from_i32(-1000).expect("Test value should convert successfully"),
            ch3: I24::try_from_i32(0).expect("Test value should convert successfully"),
            ch4: I24::try_from_i32(8388607).expect("Test value should convert successfully"), // MAX
            s: I24::try_from_i32(-8388608).expect("Test value should convert successfully"),  // MIN
        };

        // Test round-trip serialization
        let packed_bytes = original.to_packed_bytes();
        assert_eq!(packed_bytes.len(), TestDataStruct::PACKED_SIZE);

        let deserialized = TestDataStruct::from_packed_bytes(&packed_bytes)
            .expect("Test value should convert successfully");
        assert_eq!(original, deserialized);

        // Test multiple structures
        let structs = vec![original.clone(), original];
        let packed_multiple = TestDataStruct::to_packed_slice(&structs);
        assert_eq!(packed_multiple.len(), 2 * TestDataStruct::PACKED_SIZE);

        let deserialized_multiple = TestDataStruct::from_packed_slice(&packed_multiple)
            .expect("Test value should convert successfully");
        assert_eq!(structs, deserialized_multiple);

        // Test invalid length handling
        let short_bytes = vec![0u8; TestDataStruct::PACKED_SIZE - 1];
        assert!(TestDataStruct::from_packed_bytes(&short_bytes).is_none());

        let invalid_multiple = vec![0u8; TestDataStruct::PACKED_SIZE + 1];
        assert!(TestDataStruct::from_packed_slice(&invalid_multiple).is_none());
    }

    #[cfg(test)]
    mod property_tests {
        use super::*;
        use proptest::prelude::*;

        // Custom strategy to generate valid I24 values
        prop_compose! {
            fn valid_i24()(value in I24Repr::MIN..=I24Repr::MAX) -> I24 {
                I24::try_from_i32(value).expect("Test value should convert successfully")
            }
        }

        // Strategy for generating pairs of valid I24 values
        prop_compose! {
            fn i24_pair()(a in valid_i24(), b in valid_i24()) -> (I24, I24) {
                (a, b)
            }
        }

        proptest! {
            #[test]
            fn prop_to_from_i32_roundtrip(value in I24Repr::MIN..=I24Repr::MAX) {
                let i24_val = I24::try_from_i32(value).expect("Value in range should convert successfully");
                prop_assert_eq!(i24_val.to_i32(), value);
            }

            #[test]
            fn prop_wrapping_from_i32_in_range(value in I24Repr::MIN..=I24Repr::MAX) {
                let i24_val = I24::wrapping_from_i32(value);
                prop_assert_eq!(i24_val.to_i32(), value);
            }

            #[test]
            fn prop_saturating_from_i32_in_range(value in I24Repr::MIN..=I24Repr::MAX) {
                let i24_val = I24::saturating_from_i32(value);
                prop_assert_eq!(i24_val.to_i32(), value);
            }

            #[test]
            fn prop_saturating_from_i32_above_max(value in I24Repr::MAX+1..=i32::MAX) {
                let i24_val = I24::saturating_from_i32(value);
                prop_assert_eq!(i24_val, I24::MAX);
            }

            #[test]
            fn prop_saturating_from_i32_below_min(value in i32::MIN..=I24Repr::MIN-1) {
                let i24_val = I24::saturating_from_i32(value);
                prop_assert_eq!(i24_val, I24::MIN);
            }

            #[test]
            fn prop_addition_commutative((a, b) in i24_pair()) {
                prop_assert_eq!(a + b, b + a);
            }

            #[test]
            fn prop_addition_associative(a in valid_i24(), b in valid_i24(), c in valid_i24()) {
                prop_assert_eq!((a + b) + c, a + (b + c));
            }

            #[test]
            fn prop_addition_identity(a in valid_i24()) {
                prop_assert_eq!(a + I24::zero(), a);
                prop_assert_eq!(I24::zero() + a, a);
            }

            #[test]
            fn prop_subtraction_identity(a in valid_i24()) {
                prop_assert_eq!(a - I24::zero(), a);
            }

            #[test]
            fn prop_subtraction_inverse(a in valid_i24()) {
                prop_assert_eq!(a - a, I24::zero());
            }

            #[test]
            fn prop_multiplication_commutative((a, b) in i24_pair()) {
                prop_assert_eq!(a * b, b * a);
            }

            #[test]
            fn prop_multiplication_identity(a in valid_i24()) {
                prop_assert_eq!(a * I24::one(), a);
                prop_assert_eq!(I24::one() * a, a);
            }

            #[test]
            fn prop_multiplication_zero(a in valid_i24()) {
                prop_assert_eq!(a * I24::zero(), I24::zero());
                prop_assert_eq!(I24::zero() * a, I24::zero());
            }

            #[test]
            fn prop_bitwise_and_commutative((a, b) in i24_pair()) {
                prop_assert_eq!(a & b, b & a);
            }

            #[test]
            fn prop_bitwise_or_commutative((a, b) in i24_pair()) {
                prop_assert_eq!(a | b, b | a);
            }

            #[test]
            fn prop_bitwise_xor_commutative((a, b) in i24_pair()) {
                prop_assert_eq!(a ^ b, b ^ a);
            }

            #[test]
            fn prop_bitwise_xor_self_zero(a in valid_i24()) {
                prop_assert_eq!(a ^ a, I24::zero());
            }

            #[test]
            fn prop_negation_involution(a in valid_i24()) {
                // Note: This won't hold for MIN due to two's complement overflow
                if a != I24::MIN {
                    prop_assert_eq!(-(-a), a);
                }
            }

            #[test]
            fn prop_byte_roundtrip_le(a in valid_i24()) {
                let bytes = a.to_le_bytes();
                let reconstructed = I24::from_le_bytes(bytes);
                prop_assert_eq!(a, reconstructed);
            }

            #[test]
            fn prop_byte_roundtrip_be(a in valid_i24()) {
                let bytes = a.to_be_bytes();
                let reconstructed = I24::from_be_bytes(bytes);
                prop_assert_eq!(a, reconstructed);
            }

            #[test]
            fn prop_byte_roundtrip_ne(a in valid_i24()) {
                let bytes = a.to_ne_bytes();
                let reconstructed = I24::from_ne_bytes(bytes);
                prop_assert_eq!(a, reconstructed);
            }

            #[test]
            fn prop_checked_arithmetic_consistency(
                (a, b) in i24_pair()
            ) {
                // Checked arithmetic should match wrapping arithmetic when no overflow occurs
                let a_i32 = a.to_i32();
                let b_i32 = b.to_i32();

                if let Some(expected_add) = a_i32.checked_add(b_i32) {
                    if (I24Repr::MIN..=I24Repr::MAX).contains(&expected_add) {
                        prop_assert_eq!(a.checked_add(b), Some(I24::try_from_i32(expected_add).expect("Test value should convert successfully")));
                    }
                } else {
                    prop_assert_eq!(a.checked_add(b), None);
                }

                if let Some(expected_sub) = a_i32.checked_sub(b_i32) {
                    if (I24Repr::MIN..=I24Repr::MAX).contains(&expected_sub) {
                        prop_assert_eq!(a.checked_sub(b), Some(I24::try_from_i32(expected_sub).expect("Test value should convert successfully")));
                    }
                } else {
                    prop_assert_eq!(a.checked_sub(b), None);
                }

                if let Some(expected_mul) = a_i32.checked_mul(b_i32) {
                    if (I24Repr::MIN..=I24Repr::MAX).contains(&expected_mul) {
                        prop_assert_eq!(a.checked_mul(b), Some(I24::try_from_i32(expected_mul).expect("Test value should convert successfully")));
                    }
                } else {
                    prop_assert_eq!(a.checked_mul(b), None);
                }
            }

            #[test]
            fn prop_from_str_parse_display_roundtrip(a in valid_i24()) {
                let s = format!("{}", a);
                let parsed = I24::from_str(&s).expect("Test value should convert successfully");
                prop_assert_eq!(a, parsed);
            }

            #[test]
            fn prop_try_from_u8_always_succeeds(value in any::<u8>()) {
                let result = <I24 as From<u8>>::from(value);
                prop_assert_eq!(result.to_i32(), value as i32);
            }

            #[test]
            fn prop_try_from_i8_always_succeeds(value in any::<i8>()) {
                let result = <I24 as From<i8>>::from(value);
                prop_assert_eq!(result.to_i32(), value as i32);
            }

            #[test]
            fn prop_try_from_u16_always_succeeds(value in any::<u16>()) {
                let result = <I24 as From<u16>>::from(value);
                prop_assert_eq!(result.to_i32(), value as i32);
            }

            #[test]
            fn prop_try_from_i16_always_succeeds(value in any::<i16>()) {
                let result = <I24 as From<i16>>::from(value);
                prop_assert_eq!(result.to_i32(), value as i32);
            }

            #[test]
            fn prop_try_from_u32_range_check(value in any::<u32>()) {
                let result = I24::try_from(value);
                if value <= I24Repr::MAX as u32 {
                    prop_assert!(result.is_ok());
                    prop_assert_eq!(result.expect("Test value should convert successfully").to_i32(), value as i32);
                } else {
                    prop_assert!(result.is_err());
                }
            }

            #[test]
            fn prop_try_from_i32_range_check(value in any::<i32>()) {
                let result = I24::try_from(value);
                if (I24Repr::MIN..=I24Repr::MAX).contains(&value) {
                    prop_assert!(result.is_ok());
                    prop_assert_eq!(result.expect("Test value should convert successfully").to_i32(), value);
                } else {
                    prop_assert!(result.is_err());
                }
            }

            #[test]
            fn prop_shift_operations(a in valid_i24(), shift in 0u32..8u32) {
                // Test basic shift properties with small shifts to avoid overflow issues
                let shifted_left = a << shift;
                let shifted_right = a >> shift;

                // Left shift by 0 should be identity
                if shift == 0 {
                    prop_assert_eq!(shifted_left, a);
                    prop_assert_eq!(shifted_right, a);
                }

                // For very small positive values and small shifts,
                // left shift followed by right shift should recover the value
                if a.to_i32() >= 0 && a.to_i32() <= (I24Repr::MAX >> shift) {
                    let back_shifted = shifted_left >> shift;
                    prop_assert_eq!(back_shifted, a);
                }
            }

            #[cfg(feature = "alloc")]
            #[test]
            fn prop_bulk_serialization_roundtrip(values in proptest::collection::vec(valid_i24(), 0..100)) {
                // Test big-endian roundtrip
                let be_bytes = I24::write_i24s_be(&values);
                let be_reconstructed = I24::read_i24s_be(&be_bytes).expect("Test value should convert successfully");
                prop_assert_eq!(&values, &be_reconstructed);

                // Test little-endian roundtrip
                let le_bytes = I24::write_i24s_le(&values);
                let le_reconstructed = I24::read_i24s_le(&le_bytes).expect("Test value should convert successfully");
                prop_assert_eq!(&values, &le_reconstructed);

                // Test native-endian roundtrip
                let ne_bytes = I24::write_i24s_ne(&values);
                let ne_reconstructed = I24::read_i24s_ne(&ne_bytes).expect("Test value should convert successfully");
                prop_assert_eq!(&values, &ne_reconstructed);
            }

            #[test]
            fn prop_ordering_consistency(a in valid_i24(), b in valid_i24()) {
                let a_i32 = a.to_i32();
                let b_i32 = b.to_i32();

                prop_assert_eq!(a.cmp(&b), a_i32.cmp(&b_i32));
                prop_assert_eq!(a < b, a_i32 < b_i32);
                prop_assert_eq!(a <= b, a_i32 <= b_i32);
                prop_assert_eq!(a > b, a_i32 > b_i32);
                prop_assert_eq!(a >= b, a_i32 >= b_i32);
                prop_assert_eq!(a == b, a_i32 == b_i32);
                prop_assert_eq!(a != b, a_i32 != b_i32);
            }

            #[test]
            fn prop_from_str_error_handling(s in "\\PC*") {
                // Test that parsing invalid strings fails appropriately
                match I24::from_str(&s) {
                    Ok(val) => {
                        // If it succeeds, verify the value is in range
                        prop_assert!(val.to_i32() >= I24Repr::MIN);
                        prop_assert!(val.to_i32() <= I24Repr::MAX);
                    }
                    Err(e) => {
                        // Different error types should be appropriate
                        // Any error type is acceptable for invalid input strings
                        let _ = e.kind();
                    }
                }
            }
        }
    }

    #[test]
    fn test_shift_operations_with_large_counts() {
        // Test shift counts >= 24 to ensure they're properly masked
        let a = i24!(0b1);

        // Test left shifts with various counts
        assert_eq!(a << 0, i24!(0b1));
        assert_eq!(a << 1, i24!(0b10));
        assert_eq!(a << 23, I24::MIN); // 0x800000, which is the minimum negative value
        assert_eq!(a << 24, i24!(0b1)); // Should wrap around due to % 24
        assert_eq!(a << 25, i24!(0b10)); // Should be same as << 1
        assert_eq!(a << 47, I24::MIN); // Should be same as << 23
        assert_eq!(a << 48, i24!(0b1)); // Should be same as << 0

        // Test right shifts with negative values for sign extension
        let b = i24!(-1); // All bits set
        assert_eq!(b >> 0, i24!(-1));
        assert_eq!(b >> 1, i24!(-1)); // Sign extension
        assert_eq!(b >> 23, i24!(-1)); // Still all bits set due to sign extension
        assert_eq!(b >> 24, i24!(-1)); // Should be same as >> 0
        assert_eq!(b >> 25, i24!(-1)); // Should be same as >> 1
        assert_eq!(b >> 47, i24!(-1)); // Should be same as >> 23
        assert_eq!(b >> 48, i24!(-1)); // Should be same as >> 0

        // Test positive values
        let c = i24!(0x7FFFFF); // Maximum positive value
        assert_eq!(c >> 24, c); // Should be same as >> 0
        assert_eq!(c >> 25, c >> 1); // Should be same as >> 1
    }

    #[test]
    fn test_ordering_across_boundaries() {
        // Test that ordering works correctly across negative/positive boundaries
        assert!(i24!(-1) < i24!(0));
        assert!(i24!(0) < i24!(1));
        assert!(i24!(-1) < i24!(1));

        // Test MIN and MAX boundaries
        assert!(I24::MIN < i24!(-1));
        assert!(i24!(-1) < i24!(0));
        assert!(i24!(0) < i24!(1));
        assert!(i24!(1) < I24::MAX);
        assert!(I24::MIN < I24::MAX);

        // Test that I24 ordering matches i32 ordering
        for a in [-1000, -1, 0, 1, 1000] {
            for b in [-1000, -1, 0, 1, 1000] {
                let i24_a = I24::try_from_i32(a).expect("Test value should convert successfully");
                let i24_b = I24::try_from_i32(b).expect("Test value should convert successfully");

                assert_eq!(
                    i24_a < i24_b,
                    a < b,
                    "Ordering mismatch: I24({}) < I24({}) should be {}, but got {}",
                    a,
                    b,
                    a < b,
                    i24_a < i24_b
                );
                assert_eq!(
                    i24_a == i24_b,
                    a == b,
                    "Equality mismatch: I24({}) == I24({}) should be {}, but got {}",
                    a,
                    b,
                    a == b,
                    i24_a == i24_b
                );
            }
        }
    }

    #[test]
    fn test_convenience_methods() {
        // Test abs method
        assert_eq!(i24!(10).abs(), i24!(10));
        assert_eq!(i24!(-10).abs(), i24!(10));
        assert_eq!(I24::MIN.abs(), I24::MIN); // Wraps around

        // Test signum method
        assert_eq!(i24!(10).signum(), i24!(1));
        assert_eq!(i24!(0).signum(), i24!(0));
        assert_eq!(i24!(-10).signum(), i24!(-1));

        // Test is_negative/is_positive
        assert!(!i24!(10).is_negative());
        assert!(!i24!(0).is_negative());
        assert!(i24!(-10).is_negative());

        assert!(i24!(10).is_positive());
        assert!(!i24!(0).is_positive());
        assert!(!i24!(-10).is_positive());

        // Test clamp
        assert_eq!(i24!(-3).clamp(i24!(-2), i24!(1)), i24!(-2));
        assert_eq!(i24!(0).clamp(i24!(-2), i24!(1)), i24!(0));
        assert_eq!(i24!(2).clamp(i24!(-2), i24!(1)), i24!(1));

        // Test min/max
        assert_eq!(i24!(1).min(i24!(2)), i24!(1));
        assert_eq!(i24!(2).max(i24!(1)), i24!(2));
    }

    #[test]
    fn test_signed_trait() {
        use num_traits::Signed;

        // Test abs_sub method specifically
        let a = i24!(10);
        let b = i24!(5);
        let c = i24!(-3);

        // Test positive difference
        assert_eq!(a.abs_sub(&b), i24!(5)); // 10 - 5 = 5

        // Test when self <= other (should return 0)
        assert_eq!(b.abs_sub(&a), i24!(0)); // 5 - 10 <= 0, so return 0
        assert_eq!(a.abs_sub(&a), i24!(0)); // 10 - 10 = 0

        // Test with negative numbers
        assert_eq!(a.abs_sub(&c), i24!(13)); // 10 - (-3) = 13
        assert_eq!(c.abs_sub(&a), i24!(0)); // -3 - 10 <= 0, so return 0

        // Test that trait methods work correctly (should call our implementations)
        assert_eq!(Signed::abs(&i24!(10)), i24!(10));
        assert_eq!(Signed::abs(&i24!(-10)), i24!(10));
        assert_eq!(Signed::signum(&i24!(10)), i24!(1));
        assert_eq!(Signed::signum(&i24!(-10)), i24!(-1));
        assert_eq!(Signed::signum(&i24!(0)), i24!(0));
        assert!(Signed::is_positive(&i24!(10)));
        assert!(!Signed::is_positive(&i24!(-10)));
        assert!(!Signed::is_positive(&i24!(0)));
        assert!(!Signed::is_negative(&i24!(10)));
        assert!(Signed::is_negative(&i24!(-10)));
        assert!(!Signed::is_negative(&i24!(0)));

        // Test edge cases for abs_sub
        assert_eq!(I24::MAX.abs_sub(&I24::MIN), I24::MAX - I24::MIN);
        assert_eq!(I24::MIN.abs_sub(&I24::MAX), i24!(0));
    }

    #[test]
    fn test_wrapping_methods() {
        // Test that wrapping methods match operator behavior
        let a = i24!(100);
        let b = i24!(27);

        assert_eq!(a.wrapping_add(b), a + b);
        assert_eq!(a.wrapping_sub(b), a - b);
        assert_eq!(a.wrapping_mul(b), a * b);
        assert_eq!(a.wrapping_div(b), a / b);
        assert_eq!(a.wrapping_rem(b), a % b);
        assert_eq!(a.wrapping_neg(), -a);

        // Test wrapping behavior at boundaries
        assert_eq!(I24::MAX.wrapping_add(i24!(1)), I24::MIN);
        assert_eq!(I24::MIN.wrapping_sub(i24!(1)), I24::MAX);
        assert_eq!(I24::MIN.wrapping_neg(), I24::MIN);
    }

    #[test]
    fn test_saturating_methods() {
        // Test normal operations
        let a = i24!(100);
        let b = i24!(27);

        assert_eq!(a.saturating_add(b), i24!(127));
        assert_eq!(a.saturating_sub(b), i24!(73));
        assert_eq!(a.saturating_mul(b), i24!(2700));

        // Test saturation at boundaries
        assert_eq!(I24::MAX.saturating_add(i24!(1)), I24::MAX);
        assert_eq!(I24::MIN.saturating_sub(i24!(1)), I24::MIN);
        assert_eq!(I24::MIN.saturating_neg(), I24::MAX);
        assert_eq!(I24::MIN.saturating_div(i24!(-1)), I24::MAX);
    }

    #[cfg(feature = "num-cast")]
    #[test]
    fn test_num_cast_trait() {
        use num_traits::NumCast;

        // Test successful conversions from various types
        assert_eq!(
            <I24 as NumCast>::from(1000i32),
            Some(I24::try_from_i32(1000).unwrap())
        );
        assert_eq!(
            <I24 as NumCast>::from(500u16),
            Some(I24::try_from_i32(500).unwrap())
        );
        assert_eq!(
            <I24 as NumCast>::from(100i8),
            Some(I24::try_from_i32(100).unwrap())
        );
        assert_eq!(
            <I24 as NumCast>::from(200u8),
            Some(I24::try_from_i32(200).unwrap())
        );
        assert_eq!(
            <I24 as NumCast>::from(-1000i32),
            Some(I24::try_from_i32(-1000).unwrap())
        );

        // Test out of range conversions return None
        assert_eq!(<I24 as NumCast>::from(10_000_000i32), None);
        assert_eq!(<I24 as NumCast>::from(-10_000_000i32), None);
        assert_eq!(<I24 as NumCast>::from(20_000_000u32), None);

        // Test edge cases
        assert_eq!(<I24 as NumCast>::from(I24::MAX.to_i32()), Some(I24::MAX));
        assert_eq!(<I24 as NumCast>::from(I24::MIN.to_i32()), Some(I24::MIN));

        // Test floating point conversions
        assert_eq!(
            <I24 as NumCast>::from(1000.0f32),
            Some(I24::try_from_i32(1000).unwrap())
        );
        assert_eq!(
            <I24 as NumCast>::from(-500.5f32),
            Some(I24::try_from_i32(-500).unwrap())
        );
        assert_eq!(<I24 as NumCast>::from(1e10f64), None); // Too large
    }
}
#[cfg(test)]
mod wire_tests {
    use super::*;

    #[test]
    fn test_i24bytes_size_and_alignment() {
        assert_eq!(core::mem::size_of::<I24Bytes>(), 3);
        assert_eq!(core::mem::align_of::<I24Bytes>(), 1);
    }

    #[test]
    fn test_i24bytes_round_trip_le() {
        let test_values = [
            0i32, 1, -1, 123456, -123456, 8388607,  // MAX
            -8388608, // MIN
            255, -255, 65536, -65536,
        ];

        for &value in &test_values {
            let i24_val = I24::try_from(value).expect("Test value should convert successfully");
            let wire = I24Bytes::from_i24_le(i24_val);
            let recovered = wire.to_i24_le();
            assert_eq!(i24_val, recovered, "Round-trip failed for value: {}", value);
        }
    }

    #[test]
    fn test_i24bytes_round_trip_be() {
        let test_values = [
            0i32, 1, -1, 123456, -123456, 8388607,  // MAX
            -8388608, // MIN
        ];

        for &value in &test_values {
            let i24_val = I24::try_from(value).expect("Test value should convert successfully");
            let wire = I24Bytes::from_i24_be(i24_val);
            let recovered = wire.to_i24_be();
            assert_eq!(i24_val, recovered, "Round-trip failed for value: {}", value);
        }
    }

    #[test]
    fn test_i24bytes_endianness_difference() {
        let value = I24::try_from(0x123456).expect("Test value should convert successfully");
        let le_bytes = I24Bytes::from_i24_le(value);
        let be_bytes = I24Bytes::from_i24_be(value);

        // The byte arrays should be different for non-symmetric values
        assert_ne!(le_bytes.to_bytes(), be_bytes.to_bytes());

        // But they should convert to the same value when interpreted correctly
        assert_eq!(le_bytes.to_i24_le(), be_bytes.to_i24_be());
    }

    #[test]
    fn test_i24bytes_specific_byte_patterns() {
        // Test specific known byte patterns
        let le_bytes = I24Bytes([0x40, 0xE2, 0x01]); // 123456 in LE
        let be_bytes = I24Bytes([0x01, 0xE2, 0x40]); // 123456 in BE

        assert_eq!(
            le_bytes.to_i24_le(),
            I24::try_from(123456).expect("Test value should convert successfully")
        );
        assert_eq!(
            be_bytes.to_i24_be(),
            I24::try_from(123456).expect("Test value should convert successfully")
        );
    }

    #[test]
    fn test_i24bytes_from_raw_bytes() {
        let raw_bytes = [0x12, 0x34, 0x56];
        let wire = I24Bytes::from_bytes(raw_bytes);
        assert_eq!(wire.to_bytes(), raw_bytes);
    }

    #[test]
    fn test_i24bytes_bytemuck_traits() {
        // First verify that I24Bytes is indeed 3 bytes and aligned properly
        assert_eq!(core::mem::size_of::<I24Bytes>(), 3);
        assert_eq!(core::mem::align_of::<I24Bytes>(), 1);

        // Test that I24Bytes can be used with bytemuck
        let bytes = [0x12, 0x34, 0x56, 0xAB, 0xCD, 0xEF];

        // Try explicit casting to avoid confusion
        let first_i24 = I24Bytes([0x12, 0x34, 0x56]);

        // Test casting individual I24Bytes to bytes
        let first_array = [first_i24];
        let first_bytes: &[u8] = bytemuck::cast_slice(&first_array);
        assert_eq!(first_bytes, &[0x12, 0x34, 0x56]);

        // Test casting the byte array - use try_cast_slice for better error info
        let wire_slice = bytemuck::try_cast_slice::<u8, I24Bytes>(&bytes)
            .expect("Cast should succeed for properly aligned bytes");
        assert_eq!(wire_slice.len(), 2);
        assert_eq!(wire_slice[0].to_bytes(), [0x12, 0x34, 0x56]);
        assert_eq!(wire_slice[1].to_bytes(), [0xAB, 0xCD, 0xEF]);
    }

    #[test]
    fn test_i24bytes_in_simple_struct() {
        use bytemuck::{Pod, Zeroable};

        // Test I24Bytes as part of a simple struct (non-packed to avoid complications)
        #[repr(C)]
        #[derive(Copy, Clone, Debug, Pod, Zeroable)]
        struct SimpleWire {
            value: I24Bytes,
            padding: [u8; 1], // Add padding to make it clear this isn't about exact packing
        }

        let wire = SimpleWire {
            value: I24Bytes::from_i24_le(
                I24::try_from(123456).expect("Test value should convert successfully"),
            ),
            padding: [0xFF],
        };

        // Test that we can convert to bytes and back
        let bytes: [u8; 4] = bytemuck::cast(wire);
        let reconstructed: SimpleWire = bytemuck::cast(bytes);

        assert_eq!(
            reconstructed.value.to_i24_le(),
            I24::try_from(123456).expect("Test value should convert successfully")
        );
        assert_eq!(reconstructed.padding, [0xFF]);
    }

    #[test]
    fn test_i24bytes_sign_extension() {
        // Test that sign extension works correctly for negative values
        let negative_value = I24::try_from(-1).expect("Test value should convert successfully");
        let wire_le = I24Bytes::from_i24_le(negative_value);
        let wire_be = I24Bytes::from_i24_be(negative_value);

        // -1 should be 0xFFFFFF in two's complement
        let expected_bytes = [0xFF, 0xFF, 0xFF];
        assert_eq!(wire_le.to_bytes(), expected_bytes);
        assert_eq!(wire_be.to_bytes(), expected_bytes);

        // Both should convert back to -1
        assert_eq!(wire_le.to_i24_le(), negative_value);
        assert_eq!(wire_be.to_i24_be(), negative_value);
    }

    #[test]
    fn test_i24bytes_zero_initialization() {
        let zero_wire: I24Bytes = bytemuck::Zeroable::zeroed();
        assert_eq!(zero_wire.to_bytes(), [0, 0, 0]);
        assert_eq!(
            zero_wire.to_i24_le(),
            I24::try_from(0).expect("Test value should convert successfully")
        );
        assert_eq!(
            zero_wire.to_i24_be(),
            I24::try_from(0).expect("Test value should convert successfully")
        );
    }

    #[cfg(feature = "zerocopy")]
    #[test]
    fn test_i24bytes_zerocopy_traits() {
        // Test that I24Bytes implements the zerocopy traits correctly
        let bytes = [0x12, 0x34, 0x56];

        // Test that we can create from bytes and convert back
        let wire = I24Bytes::from_bytes(bytes);
        assert_eq!(wire.to_bytes(), bytes);

        // Test that I24Bytes has the expected alignment (should be 1)
        assert_eq!(core::mem::align_of::<I24Bytes>(), 1);

        // The zerocopy traits are derive-only in this version, so we mainly
        // test that the derives compiled successfully and basic functionality works
    }

    #[cfg(feature = "ndarray")]
    #[test]
    fn test_ndarray_scalar_operand() {
        // Test that I24 and I24Bytes implement ScalarOperand trait
        // This test mainly verifies the trait implementations compile correctly
        use ndarray::ScalarOperand;

        let i24_val = crate::i24!(100);
        let i24_bytes = I24Bytes([0x64, 0x00, 0x00]); // 100 in little endian

        // Test that we can use I24 as a scalar operand (trait bound check)
        fn check_scalar_operand<T: ScalarOperand>(_: T) {}
        check_scalar_operand(i24_val);
        check_scalar_operand(i24_bytes);

        // These operations should compile if ScalarOperand is properly implemented
        // Note: actual arithmetic depends on ndarray implementing ops for I24/i32
    }
}
