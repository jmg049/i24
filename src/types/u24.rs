use core::{
    fmt::{self, Binary, Debug, Display, LowerHex, Octal, UpperHex},
    hash::{Hash, Hasher},
    num::ParseIntError,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Deref,
        DerefMut, Div, DivAssign, Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr,
        ShrAssign, Sub, SubAssign,
    },
    str::FromStr,
};

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use bytemuck::{NoUninit, Pod, Zeroable};
#[cfg(feature = "num-cast")]
use num_traits::{FromPrimitive, Num, NumCast, One, ToBytes, ToPrimitive, Zero};
#[cfg(not(feature = "num-cast"))]
use num_traits::{FromPrimitive, Num, One, ToBytes, ToPrimitive, Zero};

use crate::repr::U24Repr;
use crate::{TryFromIntError, out_of_range, u24};

#[allow(non_camel_case_types)]
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
/// A 24-bit unsigned integer type.
///
/// The `U24` type represents a 24-bit unsigned integer. It provides a memory-efficient
/// alternative to `u32` when only 24 bits of precision are needed, while offering
/// a much larger range than `u16`.
///
/// This type is particularly suited to applications such as audio processing, graphics,
/// binary file manipulation, embedded systems, or networking protocols where 24-bit
/// unsigned integers are common.
///
/// ## Range
///
/// The valid value range is:
///
/// ```text
///   MIN = 0          // 0
///   MAX = 16_777_215 // 2^24 - 1
/// ```
///
/// Arithmetic operations are implemented to match Rust's standard integer behavior,
/// including overflow and checked variants.
///
/// ## Memory Layout and Safety
///
/// `U24` is implemented as a `#[repr(transparent)]` wrapper around a 4-byte internal representation.
/// Although the logical width is 24 bits, one additional byte is used for alignment and padding control.
///
/// This struct:
///
/// - Contains **no uninitialized or padding bytes**
/// - Is **safe to use** with [`bytemuck::NoUninit`](https://docs.rs/bytemuck/latest/bytemuck/trait.NoUninit.html)
/// - Can be cast safely with [`bytemuck::cast_slice`] for use in FFI and low-level applications
///
/// The layout is verified via compile-time assertions to ensure portability and correctness.
pub struct U24(U24Repr);

// Safety: repr(transparent) and so if U24Repr is Zeroable so should U24 be
unsafe impl Zeroable for U24 where U24Repr: Zeroable {}

// Safety: repr(transparent) and so if U24Repr is NoUninit so should U24 be
unsafe impl NoUninit for U24 where U24Repr: NoUninit {}

impl FromPrimitive for U24
where
    U24Repr: FromPrimitive,
{
    #[inline]
    fn from_i64(n: i64) -> Option<Self> {
        U24Repr::from_i64(n).map(Self)
    }

    #[inline]
    fn from_u64(n: u64) -> Option<Self> {
        U24Repr::from_u64(n).map(Self)
    }
}

// From<U24> for larger integer types (always succeeds)
impl From<U24> for u32 {
    #[inline]
    fn from(value: U24) -> Self {
        value.to_u32()
    }
}

impl From<U24> for u64 {
    #[inline]
    fn from(value: U24) -> Self {
        value.to_u32() as u64
    }
}

impl From<U24> for u128 {
    #[inline]
    fn from(value: U24) -> Self {
        value.to_u32() as u128
    }
}

impl From<U24> for usize {
    #[inline]
    fn from(value: U24) -> Self {
        value.to_u32() as usize
    }
}

impl U24 {
    /// The size of this integer type in bits
    pub const BITS: u32 = 24;

    /// The smallest value that can be represented by this integer type (0)
    pub const MIN: U24 = u24!(U24Repr::MIN);

    /// The largest value that can be represented by this integer type (2<sup>24</sup> − 1).
    pub const MAX: U24 = U24(unsafe { U24Repr::from_bits(U24Repr::MAX) });

    /// Creates a new `U24` with all bits set to zero.
    pub const ZERO: U24 = U24(unsafe { U24Repr::from_bits(U24Repr::ZERO) });

    /// Returns a reference to the underlying 32-bit representation.
    ///
    /// The 24-bit value is stored in the lower 24 bits, with the upper 8 bits guaranteed to be zero.
    /// This method provides direct access to the internal bit representation for advanced use cases.
    #[inline]
    pub const fn as_bits(&self) -> &u32 {
        self.0.as_bits()
    }

    #[inline]
    const fn to_bits(self) -> u32 {
        self.0.to_bits()
    }

    /// Safety: see `U24Repr::from_bits`
    #[inline]
    const unsafe fn from_bits(bits: u32) -> U24 {
        Self(unsafe { U24Repr::from_bits(bits) })
    }

    /// same as `Self::from_bits` but always truncates
    #[inline]
    const fn from_bits_truncate(bits: u32) -> U24 {
        // the most significant byte is zeroed out
        Self(unsafe { U24Repr::from_bits(bits & U24Repr::BITS_MASK) })
    }

    /// Converts the 24-bit unsigned integer to a 32-bit unsigned integer.
    ///
    /// This is a zero-extending conversion.
    ///
    /// # Returns
    ///
    /// The 32-bit unsigned integer representation of this `U24`.
    #[inline]
    pub const fn to_u32(self) -> u32 {
        self.0.to_u32()
    }

    /// Creates a `U24` from a 32-bit unsigned integer.
    ///
    /// This method truncates the input to 24 bits if it's outside the valid range.
    ///
    /// # Arguments
    ///
    /// * `n` - The 32-bit unsigned integer to convert.
    ///
    /// # Returns
    ///
    /// A `U24` instance representing the input value (truncated to 24 bits).
    #[inline]
    pub const fn wrapping_from_u32(n: u32) -> Self {
        Self(U24Repr::wrapping_from_u32(n))
    }

    /// Creates a `U24` from a 32-bit unsigned integer.
    ///
    /// This method saturates the input if it's outside the valid range.
    ///
    /// # Arguments
    ///
    /// * `n` - The 32-bit unsigned integer to convert.
    ///
    /// # Returns
    ///
    /// A `U24` instance representing the input value (saturated to the valid range).
    #[inline]
    pub const fn saturating_from_u32(n: u32) -> Self {
        Self(U24Repr::saturating_from_u32(n))
    }

    /// Reverses the byte order of the integer.
    #[inline]
    pub const fn swap_bytes(self) -> Self {
        Self(self.0.swap_bytes())
    }

    /// Converts self to little endian from the target's endianness.
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    #[inline]
    pub const fn to_le(self) -> Self {
        Self(self.0.to_le())
    }

    /// Converts self to big endian from the target's endianness.
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    #[inline]
    pub const fn to_be(self) -> Self {
        Self(self.0.to_be())
    }

    /// Return the memory representation of this integer as a byte array in native byte order.
    /// As the target platform's native endianness is used,
    /// portable code should use to_be_bytes or to_le_bytes, as appropriate, instead.
    #[inline]
    pub const fn to_ne_bytes(self) -> [u8; 3] {
        self.0.to_ne_bytes()
    }

    /// Create a native endian integer value from its representation as a byte array in little endian.
    #[inline]
    pub const fn to_le_bytes(self) -> [u8; 3] {
        self.0.to_le_bytes()
    }

    /// Return the memory representation of this integer as a byte array in big-endian (network) byte order.
    #[inline]
    pub const fn to_be_bytes(self) -> [u8; 3] {
        self.0.to_be_bytes()
    }

    /// Creates a `U24` from three bytes in **native endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit unsigned integer.
    ///
    /// # Returns
    ///
    /// A `U24` instance containing the input bytes.
    #[inline]
    pub const fn from_ne_bytes(bytes: [u8; 3]) -> Self {
        Self(U24Repr::from_ne_bytes(bytes))
    }

    /// Creates a `U24` from three bytes in **little-endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit unsigned integer in little-endian order.
    ///
    /// # Returns
    ///
    /// A `U24` instance containing the input bytes.
    #[inline]
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        Self(U24Repr::from_le_bytes(bytes))
    }

    /// Creates a `U24` from three bytes in **big-endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit unsigned integer in big-endian order.
    ///
    /// # Returns
    ///
    /// A `U24` instance with the bytes in the correct order.
    #[inline]
    pub const fn from_be_bytes(bytes: [u8; 3]) -> Self {
        Self(U24Repr::from_be_bytes(bytes))
    }

    /// Performs checked addition.
    ///
    /// # Arguments
    ///
    /// * `other` - The `U24` to add to this value.
    ///
    /// # Returns
    ///
    /// `Some(U24)` if the addition was successful, or `None` if it would overflow.
    pub fn checked_add(self, other: Self) -> Option<Self> {
        self.to_u32()
            .checked_add(other.to_u32())
            .and_then(Self::try_from_u32)
    }

    /// Performs checked subtraction.
    ///
    /// # Arguments
    ///
    /// * `other` - The `U24` to subtract from this value.
    ///
    /// # Returns
    ///
    /// `Some(U24)` if the subtraction was successful, or `None` if it would underflow.
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.to_u32()
            .checked_sub(other.to_u32())
            .and_then(Self::try_from_u32)
    }

    /// Performs checked multiplication.
    ///
    /// # Arguments
    ///
    /// * `other` - The `U24` to multiply with this value.
    ///
    /// # Returns
    ///
    /// `Some(U24)` if the multiplication was successful, or `None` if it would overflow.
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        self.to_u32()
            .checked_mul(other.to_u32())
            .and_then(Self::try_from_u32)
    }

    /// Performs checked division.
    ///
    /// # Arguments
    ///
    /// * `other` - The `U24` to divide this value by.
    ///
    /// # Returns
    ///
    /// `Some(U24)` if the division was successful, or `None` if the divisor is zero.
    pub fn checked_div(self, other: Self) -> Option<Self> {
        self.to_u32()
            .checked_div(other.to_u32())
            .and_then(Self::try_from_u32)
    }

    /// Performs checked integer remainder.
    ///
    /// # Arguments
    ///
    /// * `other` - The `U24` to divide this value by.
    ///
    /// # Returns
    ///
    /// `Some(U24)` if the remainder operation was successful, or `None` if the divisor is zero.
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        self.to_u32()
            .checked_rem(other.to_u32())
            .and_then(Self::try_from_u32)
    }

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.
    #[inline]
    pub fn wrapping_add(self, rhs: Self) -> Self {
        self + rhs // Addition already wraps
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the boundary of the type.
    #[inline]
    pub fn wrapping_sub(self, rhs: Self) -> Self {
        self - rhs // Subtraction already wraps
    }

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at the boundary of the type.
    #[inline]
    pub fn wrapping_mul(self, rhs: Self) -> Self {
        self * rhs // Multiplication already wraps
    }

    /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at the boundary of the type.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    #[inline]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        self / rhs // Division wraps (though less relevant for unsigned)
    }

    /// Wrapping (modular) remainder. Computes `self % rhs`, wrapping around at the boundary of the type.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    #[inline]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        self % rhs // Remainder wraps
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds.
    #[inline]
    pub fn saturating_add(self, rhs: Self) -> Self {
        self.to_u32()
            .saturating_add(rhs.to_u32())
            .try_into()
            .unwrap_or(Self::MAX)
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric bounds.
    #[inline]
    pub fn saturating_sub(self, rhs: Self) -> Self {
        self.to_u32()
            .saturating_sub(rhs.to_u32())
            .try_into()
            .unwrap_or(Self::MIN)
    }

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric bounds.
    #[inline]
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        let result = self.to_u32().saturating_mul(rhs.to_u32());
        Self::saturating_from_u32(result)
    }

    /// Saturating integer division. Computes `self / rhs`, saturating at the numeric bounds.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0.
    #[inline]
    pub fn saturating_div(self, rhs: Self) -> Self {
        self / rhs // Division doesn't overflow for unsigned
    }

    /// Computes the minimum of `self` and `other`.
    #[inline]
    pub fn min(self, other: Self) -> Self {
        if self <= other { self } else { other }
    }

    /// Computes the maximum of `self` and `other`.
    #[inline]
    pub fn max(self, other: Self) -> Self {
        if self >= other { self } else { other }
    }

    /// Restricts the value to a certain interval.
    ///
    /// Returns `max` if `self` is greater than `max`, and `min` if `self` is less than `min`.
    /// Otherwise, returns `self`.
    ///
    /// # Panics
    ///
    /// Panics if `min > max`.
    #[inline]
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

    /// Construct a U24 from U24Bytes in little-endian byte order.
    /// This is a convenience method for converting from the wire format.
    pub const fn from_bytes_le(bytes: U24Bytes) -> Self {
        bytes.to_u24_le()
    }

    /// Construct a U24 from U24Bytes in big-endian byte order.
    /// This is a convenience method for converting from the wire format.
    pub const fn from_bytes_be(bytes: U24Bytes) -> Self {
        bytes.to_u24_be()
    }

    /// Convert a U24 into U24Bytes in little-endian byte order.
    /// This is a convenience method for converting to the wire format.
    pub const fn to_bytes_le(self) -> U24Bytes {
        U24Bytes::from_u24_le(self)
    }

    /// Convert a U24 into U24Bytes in big-endian byte order.
    /// This is a convenience method for converting to the wire format.
    pub const fn to_bytes_be(self) -> U24Bytes {
        U24Bytes::from_u24_be(self)
    }

    /// Converts a byte slice in little-endian order to a Vec of U24 values.
    ///
    /// This method interprets the input byte slice as a sequence of 24-bit unsigned integers
    /// stored in little-endian format (least significant byte first). Each `U24` value
    /// requires exactly 3 bytes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice containing 24-bit unsigned integers in little-endian format.
    ///             The length must be a multiple of 3.
    ///
    /// # Returns
    ///
    /// `Some(Vec<U24>)` containing the parsed values, or `None` if the input slice
    /// length is not a multiple of 3.
    #[cfg(feature = "alloc")]
    pub fn read_u24s_le(bytes: &[u8]) -> Option<Vec<U24>> {
        if bytes.len() % 3 != 0 {
            return None;
        }

        let mut result = Vec::with_capacity(bytes.len() / 3);

        bytes.chunks_exact(3).for_each(|chunk| {
            result.push(U24::from_be_bytes([chunk[0], chunk[1], chunk[2]]));
        });

        Some(result)
    }

    /// Converts a byte slice in big-endian order to a Vec of U24 values.
    ///
    /// This method interprets the input byte slice as a sequence of 24-bit unsigned integers
    /// stored in big-endian format (most significant byte first). Each `U24` value
    /// requires exactly 3 bytes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice containing 24-bit unsigned integers in big-endian format.
    ///            The length must be a multiple of 3.
    ///
    /// # Returns
    ///
    /// `Some(Vec<U24>)` containing the parsed values, or `None` if the input slice
    /// length is not a multiple of 3.
    #[cfg(feature = "alloc")]
    pub fn read_u24s_be(bytes: &[u8]) -> Option<Vec<U24>> {
        if bytes.len() % 3 != 0 {
            return None;
        }

        let mut result = Vec::with_capacity(bytes.len() / 3);

        bytes.chunks_exact(3).for_each(|chunk| {
            result.push(U24::from_be_bytes([chunk[0], chunk[1], chunk[2]]));
        });

        Some(result)
    }

    /// Reads multiple `U24` values from a byte slice in little-endian format without length validation.
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
    /// A vector containing the parsed `U24` values.
    #[cfg(feature = "alloc")]
    pub unsafe fn read_u24s_le_unchecked(bytes: &[u8]) -> Vec<U24> {
        debug_assert!(bytes.len() % 3 == 0);
        let chunks: &[U24Bytes] = bytemuck::cast_slice(bytes);
        chunks.iter().map(|b| b.to_u24_le()).collect()
    }

    /// Reads multiple `U24` values from a byte slice in big-endian format without length validation.
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
    /// A vector containing the parsed `U24` values.
    #[cfg(feature = "alloc")]
    pub unsafe fn read_u24s_be_unchecked(bytes: &[u8]) -> Vec<U24> {
        debug_assert!(bytes.len() % 3 == 0);
        let chunks: &[U24Bytes] = bytemuck::cast_slice(bytes);
        chunks.iter().map(|b| b.to_u24_be()).collect()
    }

    /// Converts a slice of U24 values to a Vec of bytes in little-endian order.
    #[cfg(feature = "alloc")]
    pub fn write_u24s_le(values: &[U24]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(values.len() * 3);
        for &value in values {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        bytes
    }

    /// Converts a slice of U24 values to a Vec of bytes in big-endian order.
    #[cfg(feature = "alloc")]
    pub fn write_u24s_be(values: &[U24]) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(values.len() * 3);
        for &value in values {
            bytes.extend_from_slice(&value.to_be_bytes());
        }
        bytes
    }
}

impl Not for U24 {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        let bits = !self.to_bits();
        // Safety: we mask off the MSB to ensure it's zero
        unsafe { U24::from_bits(bits & U24Repr::BITS_MASK) }
    }
}

impl Not for &U24 {
    type Output = U24;

    #[inline]
    fn not(self) -> Self::Output {
        Not::not(*self)
    }
}

impl Shl<u32> for U24 {
    type Output = Self;

    #[inline]
    fn shl(self, rhs: u32) -> Self::Output {
        // Match Rust's standard behavior: mask shift count to bit width
        let n = rhs % 24;
        Self::from_bits_truncate(self.to_bits() << n)
    }
}

impl Shl<u32> for &U24 {
    type Output = U24;

    #[inline]
    fn shl(self, rhs: u32) -> Self::Output {
        Shl::shl(*self, rhs)
    }
}

impl Shr<u32> for U24 {
    type Output = Self;

    #[inline]
    fn shr(self, rhs: u32) -> Self::Output {
        // Match Rust's standard behavior: mask shift count to bit width
        let n = rhs % 24;
        // For unsigned right shift, just shift the bits
        unsafe { Self::from_bits(self.to_bits() >> n) }
    }
}

impl Shr<u32> for &U24 {
    type Output = U24;

    #[inline]
    fn shr(self, rhs: u32) -> Self::Output {
        Shr::shr(*self, rhs)
    }
}

impl ShrAssign<u32> for U24 {
    #[inline]
    fn shr_assign(&mut self, rhs: u32) {
        *self = Shr::shr(*self, rhs)
    }
}

impl ShlAssign<u32> for U24 {
    #[inline]
    fn shl_assign(&mut self, rhs: u32) {
        *self = Shl::shl(*self, rhs)
    }
}

impl Hash for U24 {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_u32().hash(state)
    }
}

macro_rules! from_str {
    ($meth: ident($($args: tt)*)) => {
        u32::$meth($($args)*).and_then(|n| {
            U24::try_from_u32(n).ok_or_else(|| {
                "number too large to fit in target type"
                    .parse::<u32>()
                    .unwrap_err()
            })
        })
    };
}

impl FromStr for U24 {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        from_str!(from_str(s))
    }
}

// Implement num-traits for U24
impl ToPrimitive for U24 {
    #[inline]
    fn to_i64(&self) -> Option<i64> {
        Some(U24::to_u32(*self) as i64)
    }

    #[inline]
    fn to_u64(&self) -> Option<u64> {
        Some(U24::to_u32(*self) as u64)
    }

    #[inline]
    fn to_i32(&self) -> Option<i32> {
        let val = U24::to_u32(*self);
        if val > i32::MAX as u32 {
            None
        } else {
            Some(val as i32)
        }
    }

    #[inline]
    fn to_u32(&self) -> Option<u32> {
        Some(U24::to_u32(*self))
    }
}

/// Implementation of the `NumCast` trait for `U24`.
///
/// This allows safe casting from any type that implements `ToPrimitive`
/// to `U24`. The conversion returns `None` if the source value cannot
/// be represented within the 24-bit unsigned integer range [0, 16,777,215].
/// Negative values always return `None`.
#[cfg(feature = "num-cast")]
impl NumCast for U24 {
    /// Converts a value of type `T` to `U24`.
    ///
    /// # Arguments
    ///
    /// * `n` - The value to convert, which must implement `ToPrimitive`.
    ///
    /// # Returns
    ///
    /// * `Some(U24)` if the conversion succeeds and the value is within range.
    /// * `None` if the conversion fails, the value is out of range, or negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use i24::U24;
    /// use num_traits::NumCast;
    ///
    /// // Successful conversions
    /// assert_eq!(<U24 as NumCast>::from(1000u32), Some(U24::try_from_u32(1000).unwrap()));
    /// assert_eq!(<U24 as NumCast>::from(500i16), Some(U24::try_from_u32(500).unwrap()));
    ///
    /// // Out of range or negative conversions
    /// assert_eq!(<U24 as NumCast>::from(20_000_000u32), None);
    /// assert_eq!(<U24 as NumCast>::from(-100i32), None);
    /// ```
    #[inline]
    fn from<T: ToPrimitive>(n: T) -> Option<Self> {
        // For U24, we need to handle both signed and unsigned sources
        // Try signed conversion first, then unsigned if that fails
        if let Some(as_i64) = n.to_i64() {
            // If we can convert to i64, check if it's non-negative and fits in U24
            if as_i64 >= 0 {
                return Self::try_from_i64(as_i64);
            }
        }

        // If that fails or is negative, try as unsigned
        n.to_u64().and_then(Self::try_from_u64)
    }
}

impl Zero for U24 {
    #[inline]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline]
    fn is_zero(&self) -> bool {
        Self::ZERO == *self
    }
}

impl One for U24 {
    #[inline]
    fn one() -> Self {
        Self::wrapping_from_u32(1)
    }
}

impl Num for U24 {
    type FromStrRadixErr = ParseIntError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        from_str!(from_str_radix(str, radix))
    }
}

// Implement arithmetic operations for U24 using a similar macro pattern
macro_rules! impl_U24_bin_op {
    ($(impl $op: ident = $assign: ident $assign_fn: ident { $($impl: tt)* })+) => {$(
        impl_U24_bin_op!(impl $op = $assign $assign_fn for U24 { $($impl)* });
        impl_U24_bin_op!(impl $op = $assign $assign_fn for &U24 { $($impl)* });
    )+};

    (impl $op: ident = $assign: ident $assign_fn: ident for $ty:ty {
         fn $meth: ident($self: tt, $other: ident) {
            $($impl: tt)*
         }
    }) => {
        impl $op<$ty> for U24 {
            type Output = Self;

            #[inline]
            fn $meth($self, $other: $ty) -> Self {
                $($impl)*
            }
        }

        impl $op<$ty> for &U24 {
            type Output = U24;

            #[inline]
            fn $meth(self, other: $ty) -> U24 {
                <U24 as $op<$ty>>::$meth(*self, other)
            }
        }

        impl $assign<$ty> for U24 {
            #[inline]
            fn $assign_fn(&mut self, rhs: $ty) {
                *self = $op::$meth(*self, rhs)
            }
        }
    };
}

impl_U24_bin_op! {
    impl Add = AddAssign add_assign {
        fn add(self, other) {
            Self::from_bits_truncate(self.to_bits().wrapping_add(other.to_bits()))
        }
    }

    impl Sub = SubAssign sub_assign {
        fn sub(self, other) {
            Self::from_bits_truncate(self.to_bits().wrapping_sub(other.to_bits()))
        }
    }

    impl Mul = MulAssign mul_assign {
        fn mul(self, other) {
            Self::from_bits_truncate(self.to_bits().wrapping_mul(other.to_bits()))
        }
    }

    impl Div = DivAssign div_assign {
        fn div(self, other) {
            let other_val = unsafe { U24::from_bits(other.to_bits()) };
            let result = <U24>::to_u32(self).wrapping_div(<U24>::to_u32(other_val));
            Self::wrapping_from_u32(result)
        }
    }

    impl Rem = RemAssign rem_assign {
        fn rem(self, other) {
            let other_val = unsafe { U24::from_bits(other.to_bits()) };
            let result = <U24>::to_u32(self).wrapping_rem(<U24>::to_u32(other_val));
            Self::wrapping_from_u32(result)
        }
    }

    impl BitAnd = BitAndAssign bitand_assign {
        fn bitand(self, rhs) {
            let bits = self.to_bits() & rhs.to_bits();
            // Safety: both operands have MSB = 0, so result also has MSB = 0
            unsafe { U24::from_bits(bits) }
        }
    }

    impl BitOr = BitOrAssign bitor_assign {
        fn bitor(self, rhs) {
            let bits = self.to_bits() | rhs.to_bits();
            // Safety: both operands have MSB = 0, so result also has MSB = 0
            unsafe { U24::from_bits(bits) }
        }
    }

    impl BitXor = BitXorAssign bitxor_assign {
        fn bitxor(self, rhs) {
            let bits = self.to_bits() ^ rhs.to_bits();
            // Safety: both operands have MSB = 0, so result also has MSB = 0
            unsafe { U24::from_bits(bits) }
        }
    }
}

// Implement formatting traits for U24
macro_rules! impl_U24_fmt {
    ($(impl $name: path)+) => {$(
        impl $name for U24 {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <u32 as $name>::fmt(&U24::to_u32(*self), f)
            }
        }
    )*};
}

macro_rules! impl_U24_bits_fmt {
    ($(impl $name: path)+) => {$(
        impl $name for U24 {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <u32 as $name>::fmt(&self.to_bits(), f)
            }
        }
    )*};
}

impl_U24_fmt! {
    impl Display
    impl Debug
}

impl_U24_bits_fmt! {
    impl UpperHex
    impl LowerHex
    impl Octal
    impl Binary
}

// Implement ToBytes for U24 (similar to i24)
impl ToBytes for U24 {
    type Bytes = [u8; 3];

    fn to_be_bytes(&self) -> Self::Bytes {
        U24::to_be_bytes(*self)
    }

    fn to_le_bytes(&self) -> Self::Bytes {
        U24::to_le_bytes(*self)
    }
}

macro_rules! impl_from {
    ($($ty: ty : $func_name: ident),+ $(,)?) => {$(
        impl From<$ty> for U24 {
            fn from(value: $ty) -> Self {
                Self::$func_name(value)
            }
        }

        impl U24 {
            #[doc = concat!("Creates a `U24` from a `", stringify!($ty), "` value.")]
            ///
            /// This conversion is guaranteed to succeed as the source type fits within the 24-bit range.
            pub const fn $func_name(value: $ty) -> Self {
                Self(U24Repr::$func_name(value))
            }
        }
    )+};
}

macro_rules! impl_try {
    ($($ty: ty : $func_name: ident),+ $(,)?) => {$(
        impl TryFrom<$ty> for U24 {
            type Error = TryFromIntError;

            fn try_from(value: $ty) -> Result<Self, Self::Error> {
                Self::$func_name(value).ok_or_else(out_of_range)
            }
        }

        impl U24 {
            #[doc = concat!("Tries to create a `U24` from a `", stringify!($ty), "` value.")]
            ///
            /// Returns `Some(U24)` if the value fits within the 24-bit unsigned range [0, 16,777,215],
            /// or `None` if the value is out of range.
            pub const fn $func_name(value: $ty) -> Option<Self> {
                match U24Repr::$func_name(value) {
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
}

impl_try! {
    u32: try_from_u32,
    u64: try_from_u64,
    u128: try_from_u128,
    i32: try_from_i32,
    i64: try_from_i64,
    i128: try_from_i128,
}

/// Public 3-byte wire representation of an unsigned 24-bit integer.
///
/// This type represents the exact on-wire format of an `U24` value as 3 consecutive bytes.
/// Unlike the runtime `U24` type which is 4-byte aligned, `U24Bytes` is exactly 3 bytes
/// and can be safely used in packed structs for binary deserialization.
///
/// # Safety for Mixed Packed Structs
///
/// `U24Bytes` is designed to solve the problem of mixed packed structs containing both
/// standard types (like `u32`) and 24-bit integers. Since `bytemuck::Pod` forbids
/// packed structs with native integer fields, you should use byte-oriented types
/// like `U24Bytes` in your wire structs, then convert to native types.
///
/// # Examples
///
/// ```
/// use i24::U24Bytes;
///
/// // Convert from U24 to wire format
/// let value = i24::U24::try_from(123456).unwrap();
/// let wire_bytes = U24Bytes::from_u24_le(value);
///
/// // Convert back to U24
/// let recovered = wire_bytes.to_u24_le();
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
pub struct U24Bytes(pub [u8; 3]);

// Safety: U24Bytes is transparent over [u8; 3], which is always valid for any bit pattern
unsafe impl Pod for U24Bytes {}

// Safety: U24Bytes can be safely zero-initialized
unsafe impl Zeroable for U24Bytes {}

impl U24Bytes {
    /// Converts from little-endian byte array to `U24`.
    ///
    /// Interprets the 3-byte array as a little-endian unsigned integer.
    #[inline]
    pub const fn to_u24_le(self) -> U24 {
        U24::from_le_bytes(self.0)
    }

    /// Converts from big-endian byte array to `U24`.
    ///
    /// Interprets the 3-byte array as a big-endian unsigned integer.
    #[inline]
    pub const fn to_u24_be(self) -> U24 {
        U24::from_be_bytes(self.0)
    }

    /// Converts a `U24` to little-endian byte array representation.
    ///
    /// Returns a 3-byte array with the `U24` value in little-endian format.
    #[inline]
    pub const fn from_u24_le(value: U24) -> Self {
        Self(value.to_le_bytes())
    }

    /// Converts a `U24` to big-endian byte array representation.
    ///
    /// Returns a 3-byte array with the `U24` value in big-endian format.
    #[inline]
    pub const fn from_u24_be(value: U24) -> Self {
        Self(value.to_be_bytes())
    }

    /// Creates a `U24Bytes` from a 3-byte array.
    ///
    /// This is a wrapper constructor that stores the raw bytes without interpretation.
    #[inline]
    pub const fn from_bytes(bytes: [u8; 3]) -> Self {
        Self(bytes)
    }

    /// Returns the underlying 3-byte array.
    ///
    /// Extracts the raw bytes without any endianness conversion.
    #[inline]
    pub const fn to_bytes(self) -> [u8; 3] {
        self.0
    }
}

// Additional trait implementations for U24Bytes
impl AsRef<[u8; 3]> for U24Bytes {
    #[inline]
    fn as_ref(&self) -> &[u8; 3] {
        &self.0
    }
}

impl AsMut<[u8; 3]> for U24Bytes {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8; 3] {
        &mut self.0
    }
}

impl AsRef<[u8]> for U24Bytes {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        &self.0[..]
    }
}

impl AsMut<[u8]> for U24Bytes {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0[..]
    }
}

impl From<[u8; 3]> for U24Bytes {
    #[inline]
    fn from(bytes: [u8; 3]) -> Self {
        Self(bytes)
    }
}

impl From<U24Bytes> for [u8; 3] {
    #[inline]
    fn from(i24_bytes: U24Bytes) -> Self {
        i24_bytes.0
    }
}

impl Deref for U24Bytes {
    type Target = [u8; 3];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for U24Bytes {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// PyO3 implementations for U24Bytes
#[cfg(feature = "pyo3")]
mod u24_bytes_pyo3 {
    use super::U24Bytes;
    use pyo3::{
        conversion::{FromPyObject, IntoPyObject},
        prelude::*,
    };

    // IntoPyObject implementation for U24Bytes - converts to Python bytes
    impl<'py> IntoPyObject<'py> for U24Bytes {
        type Target = pyo3::types::PyBytes;
        type Output = Bound<'py, pyo3::types::PyBytes>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(pyo3::types::PyBytes::new(py, &self.0))
        }
    }

    impl<'py> IntoPyObject<'py> for &U24Bytes {
        type Target = pyo3::types::PyBytes;
        type Output = Bound<'py, pyo3::types::PyBytes>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(pyo3::types::PyBytes::new(py, &self.0))
        }
    }

    // FromPyObject implementation for U24Bytes - converts from Python bytes
    impl<'a, 'py> FromPyObject<'a, 'py> for U24Bytes {
        type Error = pyo3::PyErr;

        fn extract(obj: pyo3::Borrowed<'a, 'py, pyo3::PyAny>) -> PyResult<Self> {
            let py_bytes: &[u8] = obj.extract()?;
            if py_bytes.len() != 3 {
                return Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "Expected exactly 3 bytes for U24Bytes, got {}",
                    py_bytes.len()
                )));
            }
            Ok(U24Bytes([py_bytes[0], py_bytes[1], py_bytes[2]]))
        }
    }
}

// Add serde support for U24
#[cfg(feature = "serde")]
mod u24_serde {
    use super::U24;

    impl serde::Serialize for U24 {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serializer.serialize_u32(self.to_u32())
        }
    }

    impl<'de> serde::Deserialize<'de> for U24 {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserializer.deserialize_any(U24Visitor)
        }
    }

    struct U24Visitor;

    #[allow(unused_macros)]
    macro_rules! impl_deserialize_infallible {
        ($([$ty: path, $visit: ident, $from: ident])+) => {$(
            fn $visit<E>(self, v: $ty) -> Result<Self::Value, E> {
                Ok(U24::$from(v))
            }
        )*};
    }

    macro_rules! impl_deserialize_fallible {
        ($([$ty: path, $visit: ident, $try_from: ident])+) => {$(
            fn $visit<E>(self, v: $ty) -> Result<Self::Value, E> where E: serde::de::Error {
                U24::$try_from(v).ok_or_else(|| E::custom("U24 out of range!"))
            }
        )*};
    }

    impl serde::de::Visitor<'_> for U24Visitor {
        type Value = U24;

        fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
            formatter.write_str("an integer between 0 and 2^24-1")
        }

        // Use wrapping conversion for u8/u16 since they always fit in U24
        fn visit_u8<E>(self, v: u8) -> Result<Self::Value, E> {
            Ok(U24::wrapping_from_u32(v as u32))
        }

        fn visit_u16<E>(self, v: u16) -> Result<Self::Value, E> {
            Ok(U24::wrapping_from_u32(v as u32))
        }

        impl_deserialize_fallible! {
            [u32, visit_u32, try_from_u32]
        }

        // Manual implementations for larger unsigned types
        fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if v > u32::MAX as u64 {
                return Err(E::custom("U24 out of range"));
            }
            U24::try_from_u32(v as u32).ok_or_else(|| E::custom("U24 out of range"))
        }

        fn visit_u128<E>(self, v: u128) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if v > u32::MAX as u128 {
                return Err(E::custom("U24 out of range"));
            }
            U24::try_from_u32(v as u32).ok_or_else(|| E::custom("U24 out of range"))
        }

        // Manual implementations for signed types
        fn visit_i32<E>(self, v: i32) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if v < 0 {
                return Err(E::custom("U24 cannot represent negative values"));
            }
            U24::try_from_u32(v as u32).ok_or_else(|| E::custom("U24 out of range"))
        }

        fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if v < 0 {
                return Err(E::custom("U24 cannot represent negative values"));
            }
            if v > u32::MAX as i64 {
                return Err(E::custom("U24 out of range"));
            }
            U24::try_from_u32(v as u32).ok_or_else(|| E::custom("U24 out of range"))
        }

        fn visit_i128<E>(self, v: i128) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            if v < 0 {
                return Err(E::custom("U24 cannot represent negative values"));
            }
            if v > u32::MAX as i128 {
                return Err(E::custom("U24 out of range"));
            }
            U24::try_from_u32(v as u32).ok_or_else(|| E::custom("U24 out of range"))
        }
    }
}

#[cfg(feature = "ndarray")]
mod ndarray_support {
    impl ndarray::ScalarOperand for crate::U24 {}
    impl ndarray::ScalarOperand for crate::U24Bytes {}
}

#[cfg(feature = "pyo3")]
pub(crate) mod python {
    use crate::U24;
    use numpy::{Element, PyArrayDescr};
    use pyo3::{
        conversion::{FromPyObject, IntoPyObject},
        exceptions::{PyOverflowError, PyValueError, PyZeroDivisionError},
        prelude::*,
        sync::PyOnceLock,
    };
    use pyo3::Py;

    /// Python wrapper for the `U24` type.
    ///
    /// This struct provides Python bindings for the 24-bit unsigned integer type,
    /// allowing `U24` values to be used from Python code via PyO3.
    #[pyclass(name = "U24")]
    pub struct PyU24 {
        /// The wrapped `U24` value.
        pub value: U24,
    }

    #[pymethods]
    impl PyU24 {
        #[new]
        fn new(value: u32) -> PyResult<Self> {
            match U24::try_from_u32(value) {
                Some(v) => Ok(PyU24 { value: v }),
                None => Err(PyValueError::new_err(format!(
                    "Value {} is out of range for U24 (0 to 16777215)",
                    value
                ))),
            }
        }

        #[staticmethod]
        fn from_bytes(bytes: &[u8], byteorder: &str) -> PyResult<Self> {
            if bytes.len() != 3 {
                return Err(PyValueError::new_err("bytes must be exactly 3 bytes long"));
            }
            let byte_array: [u8; 3] = [bytes[0], bytes[1], bytes[2]];
            let value = match byteorder {
                "little" => U24::from_le_bytes(byte_array),
                "big" => U24::from_be_bytes(byte_array),
                "native" => U24::from_ne_bytes(byte_array),
                _ => {
                    return Err(PyValueError::new_err(
                        "byteorder must be 'little', 'big', or 'native'",
                    ));
                }
            };
            Ok(PyU24 { value })
        }

        fn to_int(&self) -> u32 {
            self.value.to_u32()
        }

        fn to_bytes(&self, byteorder: &str) -> PyResult<Vec<u8>> {
            let bytes = match byteorder {
                "little" => self.value.to_le_bytes(),
                "big" => self.value.to_be_bytes(),
                "native" => self.value.to_ne_bytes(),
                _ => {
                    return Err(PyValueError::new_err(
                        "byteorder must be 'little', 'big', or 'native'",
                    ));
                }
            };
            Ok(bytes.to_vec())
        }

        fn __str__(&self) -> String {
            format!("{}", self.value.to_u32())
        }

        fn __repr__(&self) -> String {
            format!("U24({})", self.value.to_u32())
        }

        fn __int__(&self) -> u32 {
            self.value.to_u32()
        }

        // Comparison operators
        fn __eq__(&self, other: &PyU24) -> bool {
            self.value == other.value
        }

        fn __ne__(&self, other: &PyU24) -> bool {
            self.value != other.value
        }

        fn __lt__(&self, other: &PyU24) -> bool {
            self.value < other.value
        }

        fn __le__(&self, other: &PyU24) -> bool {
            self.value <= other.value
        }

        fn __gt__(&self, other: &PyU24) -> bool {
            self.value > other.value
        }

        fn __ge__(&self, other: &PyU24) -> bool {
            self.value >= other.value
        }

        // Cross-type comparisons with Python int
        fn __eq_int__(&self, other: u32) -> bool {
            self.value.to_u32() == other
        }

        fn __ne_int__(&self, other: u32) -> bool {
            self.value.to_u32() != other
        }

        fn __lt_int__(&self, other: u32) -> bool {
            self.value.to_u32() < other
        }

        fn __le_int__(&self, other: u32) -> bool {
            self.value.to_u32() <= other
        }

        fn __gt_int__(&self, other: u32) -> bool {
            self.value.to_u32() > other
        }

        fn __ge_int__(&self, other: u32) -> bool {
            self.value.to_u32() >= other
        }

        // Arithmetic operators
        fn __add__(&self, other: &PyU24) -> PyResult<PyU24> {
            match self.value.checked_add(other.value) {
                Some(result) => Ok(PyU24 { value: result }),
                None => Err(PyOverflowError::new_err("U24 addition overflow")),
            }
        }

        fn __sub__(&self, other: &PyU24) -> PyResult<PyU24> {
            match self.value.checked_sub(other.value) {
                Some(result) => Ok(PyU24 { value: result }),
                None => Err(PyOverflowError::new_err("U24 subtraction overflow")),
            }
        }

        fn __mul__(&self, other: &PyU24) -> PyResult<PyU24> {
            match self.value.checked_mul(other.value) {
                Some(result) => Ok(PyU24 { value: result }),
                None => Err(PyOverflowError::new_err("U24 multiplication overflow")),
            }
        }

        fn __truediv__(&self, other: &PyU24) -> PyResult<f64> {
            if other.value.to_u32() == 0 {
                return Err(PyZeroDivisionError::new_err("division by zero"));
            }
            Ok(self.value.to_u32() as f64 / other.value.to_u32() as f64)
        }

        fn __floordiv__(&self, other: &PyU24) -> PyResult<PyU24> {
            match self.value.checked_div(other.value) {
                Some(result) => Ok(PyU24 { value: result }),
                None => Err(PyZeroDivisionError::new_err("division by zero")),
            }
        }

        fn __mod__(&self, other: &PyU24) -> PyResult<PyU24> {
            match self.value.checked_rem(other.value) {
                Some(result) => Ok(PyU24 { value: result }),
                None => Err(PyZeroDivisionError::new_err("division by zero")),
            }
        }

        // Bitwise operations
        fn __and__(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32() & other.value.to_u32();
            PyU24 {
                value: U24::wrapping_from_u32(result),
            }
        }

        fn __or__(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32() | other.value.to_u32();
            PyU24 {
                value: U24::wrapping_from_u32(result),
            }
        }

        fn __xor__(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32() ^ other.value.to_u32();
            PyU24 {
                value: U24::wrapping_from_u32(result),
            }
        }

        fn __lshift__(&self, other: u32) -> PyResult<PyU24> {
            if other >= 32 {
                return Err(PyValueError::new_err("shift count out of range"));
            }
            let result = self.value.to_u32() << other;
            match U24::try_from_u32(result) {
                Some(val) => Ok(PyU24 { value: val }),
                None => Err(PyOverflowError::new_err("U24 left shift overflow")),
            }
        }

        fn __rshift__(&self, other: u32) -> PyResult<PyU24> {
            if other >= 32 {
                return Err(PyValueError::new_err("shift count out of range"));
            }
            let result = self.value.to_u32() >> other;
            Ok(PyU24 {
                value: U24::wrapping_from_u32(result),
            })
        }

        // Utility methods
        #[staticmethod]
        fn min_value() -> PyU24 {
            PyU24 { value: U24::MIN }
        }

        #[staticmethod]
        fn max_value() -> PyU24 {
            PyU24 { value: U24::MAX }
        }

        fn count_ones(&self) -> u32 {
            self.value.to_u32().count_ones()
        }

        fn count_zeros(&self) -> u32 {
            self.value.to_u32().count_zeros()
        }

        fn leading_zeros(&self) -> u32 {
            self.value.to_u32().leading_zeros()
        }

        fn trailing_zeros(&self) -> u32 {
            self.value.to_u32().trailing_zeros()
        }

        // Checked methods
        fn checked_add(&self, other: &PyU24) -> Option<PyU24> {
            self.value
                .checked_add(other.value)
                .map(|v| PyU24 { value: v })
        }

        fn checked_sub(&self, other: &PyU24) -> Option<PyU24> {
            self.value
                .checked_sub(other.value)
                .map(|v| PyU24 { value: v })
        }

        fn checked_mul(&self, other: &PyU24) -> Option<PyU24> {
            self.value
                .checked_mul(other.value)
                .map(|v| PyU24 { value: v })
        }

        fn checked_div(&self, other: &PyU24) -> Option<PyU24> {
            self.value
                .checked_div(other.value)
                .map(|v| PyU24 { value: v })
        }

        fn wrapping_add(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32().wrapping_add(other.value.to_u32());
            PyU24 {
                value: U24::wrapping_from_u32(result),
            }
        }

        fn wrapping_sub(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32().wrapping_sub(other.value.to_u32());
            PyU24 {
                value: U24::wrapping_from_u32(result),
            }
        }

        fn wrapping_mul(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32().wrapping_mul(other.value.to_u32());
            PyU24 {
                value: U24::wrapping_from_u32(result),
            }
        }

        fn saturating_add(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32().saturating_add(other.value.to_u32());
            PyU24 {
                value: U24::saturating_from_u32(result),
            }
        }

        fn saturating_sub(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32().saturating_sub(other.value.to_u32());
            PyU24 {
                value: U24::saturating_from_u32(result),
            }
        }

        fn saturating_mul(&self, other: &PyU24) -> PyU24 {
            let result = self.value.to_u32().saturating_mul(other.value.to_u32());
            PyU24 {
                value: U24::saturating_from_u32(result),
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

        fn __pos__(&self) -> PyU24 {
            PyU24 { value: self.value }
        }

        fn __invert__(&self) -> PyU24 {
            let inverted = !self.value;
            PyU24 { value: inverted }
        }

        // Pythonic method names
        fn bit_length(&self) -> u32 {
            32 - self.value.to_u32().leading_zeros()
        }

        fn bit_count(&self) -> u32 {
            self.value.to_u32().count_ones()
        }

        fn as_integer_ratio(&self) -> (u32, u32) {
            (self.value.to_u32(), 1)
        }

        #[pyo3(signature = (ndigits = None))]
        fn __round__(&self, ndigits: Option<i32>) -> PyResult<PyU24> {
            match ndigits {
                None => Ok(PyU24 { value: self.value }),
                Some(0) => Ok(PyU24 { value: self.value }),
                Some(_) => Ok(PyU24 { value: self.value }),
            }
        }

        fn __ceil__(&self) -> PyU24 {
            PyU24 { value: self.value }
        }

        fn __floor__(&self) -> PyU24 {
            PyU24 { value: self.value }
        }

        fn __trunc__(&self) -> PyU24 {
            PyU24 { value: self.value }
        }
    }

    unsafe impl Element for U24 {
        const IS_COPY: bool = true;

        fn clone_ref(&self, _py: Python<'_>) -> Self {
            *self
        }

        fn get_dtype(py: Python<'_>) -> Bound<'_, PyArrayDescr> {
            // IMPORTANT: do not call `numpy::dtype::<U24>` here; that dispatches to
            // `U24::get_dtype` and will recurse.
            //
            // `U24` is a transparent wrapper over a `u32` representation where the top byte
            // is always zero, so exposing it as `uint32` is a correct and useful NumPy dtype.
            static DTYPE: PyOnceLock<Py<PyArrayDescr>> = PyOnceLock::new();

            DTYPE
                .get_or_init(py, || numpy::dtype::<u32>(py).unbind())
                .clone_ref(py)
                .into_bound(py)
        }
    }

    // IntoPyObject implementation for U24 - converts to Python int
    impl<'py> IntoPyObject<'py> for U24 {
        type Target = pyo3::types::PyInt;
        type Output = Bound<'py, pyo3::types::PyInt>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(self.to_u32().into_pyobject(py)?)
        }
    }

    impl<'py> IntoPyObject<'py> for &U24 {
        type Target = pyo3::types::PyInt;
        type Output = Bound<'py, pyo3::types::PyInt>;
        type Error = pyo3::PyErr;

        fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
            Ok(self.to_u32().into_pyobject(py)?)
        }
    }

    // FromPyObject implementation for U24 - converts from Python int
    impl<'a, 'py> FromPyObject<'a, 'py> for U24 {
        type Error = pyo3::PyErr;

        fn extract(obj: pyo3::Borrowed<'a, 'py, pyo3::PyAny>) -> PyResult<Self> {
            let py_int: u32 = obj.extract()?;
            U24::try_from_u32(py_int).ok_or_else(|| {
                pyo3::exceptions::PyOverflowError::new_err(format!(
                    "Value {} is out of range for U24 (0 to 16777215)",
                    py_int
                ))
            })
        }
    }
}

#[cfg(test)]
mod tests {

    #[cfg(feature = "ndarray")]
    #[test]
    fn test_ndarray_scalar_operand() {
        // Test that U24 and U24Bytes implement ScalarOperand trait
        // This test mainly verifies the trait implementations compile correctly
        use ndarray::ScalarOperand;

        let u24_val = crate::u24!(100);
        let u24_bytes = super::U24Bytes([0x64, 0x00, 0x00]); // 100 in little endian

        // Test that we can use U24 as a scalar operand (trait bound check)
        fn check_scalar_operand<T: ScalarOperand>(_: T) {}
        check_scalar_operand(u24_val);
        check_scalar_operand(u24_bytes);

        // These operations should compile if ScalarOperand is properly implemented
        // Note: actual arithmetic depends on ndarray implementing ops for U24/u32
    }

    #[cfg(feature = "num-cast")]
    #[test]
    fn test_num_cast_trait() {
        use super::U24;
        use num_traits::NumCast;

        // Test successful conversions from various types
        assert_eq!(
            <U24 as NumCast>::from(1000u32),
            Some(U24::try_from_u32(1000).unwrap())
        );
        assert_eq!(
            <U24 as NumCast>::from(500u16),
            Some(U24::try_from_u32(500).unwrap())
        );
        assert_eq!(
            <U24 as NumCast>::from(100u8),
            Some(U24::try_from_u32(100).unwrap())
        );
        assert_eq!(
            <U24 as NumCast>::from(200i16),
            Some(U24::try_from_u32(200).unwrap())
        );
        assert_eq!(
            <U24 as NumCast>::from(50i8),
            Some(U24::try_from_u32(50).unwrap())
        );

        // Test out of range conversions return None
        assert_eq!(<U24 as NumCast>::from(20_000_000u32), None);
        assert_eq!(<U24 as NumCast>::from(-100i32), None); // Negative values
        assert_eq!(<U24 as NumCast>::from(-1i8), None); // Negative values

        // Test edge cases
        assert_eq!(<U24 as NumCast>::from(U24::MAX.to_u32()), Some(U24::MAX));
        assert_eq!(<U24 as NumCast>::from(U24::MIN.to_u32()), Some(U24::MIN));

        // Test floating point conversions
        assert_eq!(
            <U24 as NumCast>::from(1000.0f32),
            Some(U24::try_from_u32(1000).unwrap())
        );
        assert_eq!(
            <U24 as NumCast>::from(500.9f32),
            Some(U24::try_from_u32(500).unwrap())
        ); // Truncated
        assert_eq!(<U24 as NumCast>::from(1e10f64), None); // Too large
        assert_eq!(<U24 as NumCast>::from(-100.0f32), None); // Negative
    }
}
