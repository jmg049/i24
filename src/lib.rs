#![no_std]

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
//! i24 = "2.1.0"
//! ```
//!
//! Then, in your Rust code:
//!
//! ```rust
//! # #[macro_use] extern crate i24;
//!
//! let a = i24!(1000);
//! let b = i24!(2000);
//! let c = a + b;
//! assert_eq!(c.to_i32(), 3000);
//! assert_eq!(c, i24!(3000));
//! ```
//! The `i24!` macro allows you to create `i24` values at compile time, ensuring that the value is within the valid range.
//!
//! Then if working with 3-byte representations from disk or the network, you can use the `I24DiskMethods` trait to read and write `i24` slices of `i24`.
//!
//!  ```ignore
//! use i24::I24DiskMethods; // Bring extension trait into scope
//! use i24::i24 as I24; // Import the i24 type
//! let raw_data: &[u8] = &[0x00, 0x01, 0x02, 0x00, 0x01, 0xFF]; // 2 values
//! let values: Vec<I24> = I24::read_i24s_be(raw_data).expect("valid buffer");
//!
//! let encoded: Vec<u8> = I24::write_i24s_be(&values);
//! assert_eq!(encoded, raw_data);
//! ```
//!
//!  ## Safety and Limitations
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
//! 'i24' aligns with the safety requirements of bytemuck (NoUninit, Zeroable and bytemuck::AnyBitPattern), ensuring that it is safe to use for converting between valid bytes and a i24 value.
//! Then when using the `I24DiskMethods` trait, it is safe to use (internally) the `bytemuck::cast_slice` function to convert between a slice of bytes and a slice of 'i24' values.
//!
//! ## Features
//! - **pyo3**: Enables the pyo3 bindings for the `i24` type.
//! - **serde**: Enables the `Serialize` and `Deserialize` traits for the `i24` type.
//! - **alloc**: Enables the `I24DiskMethods` trait for the `i24` type.
//!
//! ## Contributing
//!
//! Contributions are welcome! Please feel free to submit a Pull Request. This really needs more testing and verification.
//!
//! ## License
//!
//! This project is licensed under MIT - see the [LICENSE](https://github.com/jmg049/i24/blob/main/LICENSE) file for details.
//!
//! ## Benchmarks
//! See the [benchmark report](https://github.com/jmg049/i24/i24_benches/benchmark_analysis/benchmark_report.md).
//!

use crate::repr::I24Repr;
use bytemuck::{NoUninit, Zeroable};

#[cfg(feature = "alloc")]
use repr::DiskI24;

#[cfg(feature = "alloc")]
use bytemuck::cast_slice;

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
use num_traits::{Num, One, ToBytes, Zero};

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "pyo3")]
use numpy::PyArrayDescr;

#[cfg(feature = "std")]
extern crate std;

mod repr;

#[allow(non_camel_case_types)]
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
#[cfg_attr(feature = "pyo3", pyclass)]
/// A signed 24-bit integer type.
///
/// The `i24` type represents a 24-bit signed integer in two's complement format. It fills the gap between
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
/// `i24` is implemented as a `#[repr(transparent)]` wrapper around a 4-byte internal representation.
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
/// Although `i24` occupies 4 bytes in memory, binary formats (e.g., WAV files, network protocols) often
/// store 24-bit integers in a 3-byte representation. To support this:
///
/// - `i24` provides [`from_be_bytes`], [`from_le_bytes`], and [`from_ne_bytes`] methods for constructing
///   values from 3-byte on-disk representations
/// - Corresponding [`to_be_bytes`], [`to_le_bytes`], and [`to_ne_bytes`] methods convert to 3-byte representations
///
/// For efficient bulk deserialization, use the [`I24DiskMethods`] extension trait.
///
///  Note: Requires the ``alloc`` feature to be enabled.
///
/// ```ignore
/// use i24::I24DiskMethods;
/// use i24::i24 as I24;
/// let raw: &[u8] = &[0x00, 0x00, 0x01, 0xFF, 0xFF, 0xFF];
/// let values = I24::read_i24s_be(raw).unwrap();
/// assert_eq!(values[0].to_i32(), 1);
/// assert_eq!(values[1].to_i32(), -1);
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
/// - **`pyo3`**: Exposes the `i24` type to Python via PyO3 bindings (as `I24`)
/// - **`alloc`**: Enables `I24DiskMethods` for efficient bulk serialization/deserialization
pub struct i24(I24Repr);

// Safety: repr(transparent) and so if I24Repr is Zeroable so should i24 be
unsafe impl Zeroable for i24 where I24Repr: Zeroable {}

// Safety: repr(transparent) and so if I24Repr is NoUninit so should i24 be
// Must be NoUninit due to the padding byte.
unsafe impl NoUninit for i24 where I24Repr: NoUninit {}

#[doc(hidden)]
pub mod __macros__ {
    pub use bytemuck::Zeroable;
}

/// creates an `i24` from a constant expression
/// will give a compile error if the expression overflows an i24
#[macro_export]
macro_rules! i24 {
    (0) => {
        <i24 as $crate::__macros__::Zeroable>::zeroed()
    };
    ($e: expr) => {
        const {
            match $crate::i24::try_from_i32($e) {
                Some(x) => x,
                None => panic!(concat!(
                    "out of range value ",
                    stringify!($e),
                    " used as an i24 constant"
                )),
            }
        }
    };
}

impl i24 {
    /// The size of this integer type in bits
    pub const BITS: u32 = 24;

    /// The smallest value that can be represented by this integer type (-2<sup>23</sup>)
    pub const MIN: i24 = i24!(I24Repr::MIN);

    /// The largest value that can be represented by this integer type (2<sup>23</sup> − 1).
    pub const MAX: i24 = i24!(I24Repr::MAX);

    #[inline(always)]
    const fn as_bits(&self) -> &u32 {
        self.0.as_bits()
    }

    #[inline(always)]
    const fn to_bits(self) -> u32 {
        self.0.to_bits()
    }

    /// Safety: see `I24Repr::from_bits`
    #[inline(always)]
    const unsafe fn from_bits(bits: u32) -> i24 {
        Self(unsafe { I24Repr::from_bits(bits) })
    }

    /// same as `Self::from_bits` but always truncates
    #[inline(always)]
    const fn from_bits_truncate(bits: u32) -> i24 {
        // the most significant byte is zeroed out
        Self(unsafe { I24Repr::from_bits(bits & I24Repr::BITS_MASK) })
    }

    /// Converts the 24-bit integer to a 32-bit signed integer.
    ///
    /// This method performs sign extension if the 24-bit integer is negative.
    ///
    /// # Returns
    ///
    /// The 32-bit signed integer representation of this `i24`.
    #[inline(always)]
    pub const fn to_i32(self) -> i32 {
        self.0.to_i32()
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
    #[inline(always)]
    pub const fn wrapping_from_i32(n: i32) -> Self {
        Self(I24Repr::wrapping_from_i32(n))
    }

    /// Creates an `i24` from a 32-bit signed integer.
    ///
    /// This method saturates the input if it's outside the valid range.
    ///
    /// # Arguments
    ///
    /// * `n` - The 32-bit signed integer to convert.
    ///
    /// # Returns
    ///
    /// An `i24` instance representing the input value.
    #[inline(always)]
    pub const fn saturating_from_i32(n: i32) -> Self {
        Self(I24Repr::saturating_from_i32(n))
    }

    /// Reverses the byte order of the integer.
    #[inline(always)]
    pub const fn swap_bytes(self) -> Self {
        Self(self.0.swap_bytes())
    }

    /// Converts self to little endian from the target's endianness.
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    #[inline(always)]
    pub const fn to_le(self) -> Self {
        Self(self.0.to_le())
    }

    /// Converts self to big endian from the target's endianness.
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    #[inline(always)]
    pub const fn to_be(self) -> Self {
        Self(self.0.to_be())
    }

    /// Return the memory representation of this integer as a byte array in native byte order.
    /// As the target platform's native endianness is used,
    /// portable code should use to_be_bytes or to_le_bytes, as appropriate, instead.
    #[inline(always)]
    pub const fn to_ne_bytes(self) -> [u8; 3] {
        self.0.to_ne_bytes()
    }

    /// Create a native endian integer value from its representation as a byte array in little endian.
    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 3] {
        self.0.to_le_bytes()
    }

    /// Return the memory representation of this integer as a byte array in big-endian (network) byte order.
    #[inline(always)]
    pub const fn to_be_bytes(self) -> [u8; 3] {
        self.0.to_be_bytes()
    }

    /// Creates an `i24` from three bytes in **native endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer.
    ///
    /// # Returns
    ///
    /// An `i24` instance containing the input bytes.
    #[inline(always)]
    pub const fn from_ne_bytes(bytes: [u8; 3]) -> Self {
        Self(I24Repr::from_ne_bytes(bytes))
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
    #[inline(always)]
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        Self(I24Repr::from_le_bytes(bytes))
    }

    /// Creates an `i24` from three bytes in **big-endian** order.
    ///
    /// # Arguments
    ///
    /// * `bytes` - An array of 3 bytes representing the 24-bit integer in big-endian order.
    ///
    /// # Returns
    ///
    /// An `i24` instance with the bytes in little-endian order.
    #[inline(always)]
    pub const fn from_be_bytes(bytes: [u8; 3]) -> Self {
        Self(I24Repr::from_be_bytes(bytes))
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
            .and_then(Self::try_from_i32)
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
            .and_then(Self::try_from_i32)
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
            .and_then(Self::try_from_i32)
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
            .and_then(Self::try_from_i32)
    }

    /// Performs checked integer remainder.
    ///
    /// # Arguments
    ///
    /// * `other` - The `i24` to divide this value by.
    ///
    /// # Returns
    ///
    /// `Some(i24)` if the remainder operation was successful, or `None` if the divisor is zero or if the division would overflow.
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        self.to_i32()
            .checked_rem(other.to_i32())
            .and_then(Self::try_from_i32)
    }
}

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// Extension trait for performing efficient binary (de)serialization of [`i24`] values.
///
/// This trait provides methods to read and write slices of [`i24`] values to and from
/// raw byte buffers using standard 3-byte representations in various byte orders.
///
/// These methods are especially useful when working with binary formats like audio files,
/// network protocols, or memory-mapped files that use 24-bit integer encodings.
///
/// The methods support safe and zero-copy deserialization using [`bytemuck::cast_slice`],
/// under the guarantee that the on-disk format is valid and byte-aligned.
///
/// ## Usage
///
/// This trait is not implemented on `[u8]` or `[i24]` directly.
/// Instead, you must import the trait and call methods via the [`i24`] type:
///
/// ```rust
/// use i24::I24DiskMethods; // Bring extension trait into scope
/// use i24::i24 as I24; // Import the i24 type
/// let raw_data: &[u8] = &[0x00, 0x01, 0x02, 0x00, 0x01, 0xFF]; // 2 values
/// let values: Vec<I24> = I24::read_i24s_be(raw_data).expect("valid buffer");
///
/// let encoded: Vec<u8> = I24::write_i24s_be(&values);
/// assert_eq!(encoded, raw_data);
/// ```
///
/// ### Byte Order
///
/// Each method clearly indicates the expected byte order:
///
/// - `*_be`: Big-endian (most significant byte first)
/// - `*_le`: Little-endian
/// - `*_ne`: Native-endian (depends on target platform)
///
/// ## Safety
///
/// The `*_unchecked` variants skip input validation and assume:
///
/// - The input slice length is a multiple of 3
/// - The slice is properly aligned and valid for casting to a [`crate::DiskI24`]
///
#[cfg(feature = "alloc")]
pub trait I24DiskMethods {
    fn read_i24s_be(bytes: &[u8]) -> Option<Vec<i24>> {
        if bytes.len() % 3 != 0 {
            return None;
        }

        let chunks: &[DiskI24] = cast_slice(bytes); // Safe: NoUninit, packed, 3-byte chunks
        Some(chunks.iter().map(|b| i24::from_be_bytes(b.bytes)).collect())
    }

    unsafe fn read_i24s_be_unchecked(bytes: &[u8]) -> Vec<i24> {
        let chunks: &[DiskI24] = cast_slice(bytes); // Safe: NoUninit, packed, 3-byte chunks
        chunks.iter().map(|b| i24::from_be_bytes(b.bytes)).collect()
    }

    fn write_i24s_be(values: &[i24]) -> Vec<u8> {
        values.iter().flat_map(|v| v.to_be_bytes()).collect()
    }

    fn read_i24s_le(bytes: &[u8]) -> Option<Vec<i24>> {
        if bytes.len() % 3 != 0 {
            return None;
        }

        let chunks: &[DiskI24] = cast_slice(bytes); // Safe: NoUninit, packed, 3-byte chunks
        Some(chunks.iter().map(|b| i24::from_le_bytes(b.bytes)).collect())
    }

    unsafe fn read_i24s_le_unchecked(bytes: &[u8]) -> Vec<i24> {
        let chunks: &[DiskI24] = cast_slice(bytes); // Safe: NoUninit, packed, 3-byte chunks
        chunks.iter().map(|b| i24::from_le_bytes(b.bytes)).collect()
    }

    fn write_i24s_le(values: &[i24]) -> Vec<u8> {
        values.iter().flat_map(|v| v.to_le_bytes()).collect()
    }

    fn read_i24s_ne(bytes: &[u8]) -> Option<Vec<i24>> {
        if bytes.len() % 3 != 0 {
            return None;
        }

        let chunks: &[DiskI24] = cast_slice(bytes); // Safe: NoUninit, packed, 3-byte chunks
        Some(chunks.iter().map(|b| i24::from_ne_bytes(b.bytes)).collect())
    }

    unsafe fn read_i24s_ne_unchecked(bytes: &[u8]) -> Vec<i24> {
        let chunks: &[DiskI24] = cast_slice(bytes); // Safe: NoUninit, packed, 3-byte chunks
        chunks.iter().map(|b| i24::from_ne_bytes(b.bytes)).collect()
    }

    fn write_i24s_ne(values: &[i24]) -> Vec<u8> {
        values.iter().flat_map(|v| v.to_ne_bytes()).collect()
    }
}

#[cfg(feature = "alloc")]
impl I24DiskMethods for i24 {}

type TryFromIntError = <i8 as TryFrom<i64>>::Error;

fn out_of_range() -> TryFromIntError {
    i8::try_from(i64::MIN).unwrap_err()
}

macro_rules! impl_from {
    ($($ty: ty : $func_name: ident),+ $(,)?) => {$(
        impl From<$ty> for i24 {
            fn from(value: $ty) -> Self {
                Self::$func_name(value)
            }
        }

        impl i24 {
            pub const fn $func_name(value: $ty) -> Self {
                Self(I24Repr::$func_name(value))
            }
        }
    )+};
}

macro_rules! impl_try {
    ($($ty: ty : $func_name: ident),+ $(,)?) => {$(
        impl TryFrom<$ty> for i24 {
            type Error = TryFromIntError;

            fn try_from(value: $ty) -> Result<Self, Self::Error> {
                Self::$func_name(value).ok_or_else(out_of_range)
            }
        }

        impl i24 {
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

impl One for i24 {
    fn one() -> Self {
        i24!(1)
    }
}

impl Zero for i24 {
    #[inline(always)]
    fn zero() -> Self {
        Self::zeroed()
    }

    #[inline(always)]
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

const POSITIVE_OVERFLOW: ParseIntError =from_str_error("9999999999999999999999999999999999999999");

const NEGATIVE_OVERFLOW: ParseIntError = from_str_error("-9999999999999999999999999999999999999999");

macro_rules! from_str {
    ($meth: ident($($args: tt)*)) => {
        i32::$meth($($args)*)
            .and_then(|x| i24::try_from_i32(x).ok_or_else(|| {
                if x < 0 {
                    NEGATIVE_OVERFLOW
                } else {
                    POSITIVE_OVERFLOW
                }
            }))
    };
}

impl Num for i24 {
    type FromStrRadixErr = ParseIntError;
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        from_str!(from_str_radix(str, radix))
    }
}

impl FromStr for i24 {
    type Err = ParseIntError;

    fn from_str(str: &str) -> Result<Self, Self::Err> {
        from_str!(from_str(str))
    }
}

macro_rules! impl_bin_op {
    ($(impl $op: ident = $assign: ident $assign_fn: ident { $($impl: tt)* })+) => {$(
        impl_bin_op!(impl $op = $assign $assign_fn for i24 { $($impl)* });
        impl_bin_op!(impl $op = $assign $assign_fn for &i24 { $($impl)* });
    )+};

    (impl $op: ident = $assign: ident $assign_fn: ident for $ty:ty {
         fn $meth: ident($self: tt, $other: ident) {
            $($impl: tt)*
         }
    }) => {
        impl $op<$ty> for i24 {
            type Output = Self;

            #[inline(always)]
            fn $meth($self, $other: $ty) -> Self {
                $($impl)*
            }
        }

        impl $op<$ty> for &i24 {
            type Output = i24;

            #[inline(always)]
            fn $meth(self, other: $ty) -> i24 {
                <i24 as $op<$ty>>::$meth(*self, other)
            }
        }

        impl $assign<$ty> for i24 {
            #[inline(always)]
            fn $assign_fn(&mut self, rhs: $ty) {
                *self = $op::$meth(*self, rhs)
            }
        }
    };
}

impl_bin_op! {
    impl Add = AddAssign add_assign {
        fn add(self, other) {
            // we use twos compliment and so signed and unsigned addition are strictly the same
            // so no need to cast to an i32
            Self::from_bits_truncate(self.to_bits().wrapping_add(other.to_bits()))
        }
    }

    impl Sub = SubAssign sub_assign {
        fn sub(self, other) {
            // we use twos compliment and so signed and unsigned subtraction are strictly the same
            // so no need to cast to an i32
            Self::from_bits_truncate(self.to_bits().wrapping_sub(other.to_bits()))
        }
    }

    impl Mul = MulAssign mul_assign {
        fn mul(self, other) {
            // we use twos compliment and so signed and unsigned non-widening multiplication are strictly the same
            // so no need to cast to an i32
            Self::from_bits_truncate(self.to_bits().wrapping_mul(other.to_bits()))
        }
    }

    impl Div = DivAssign div_assign {
        fn div(self, other) {
            let result = self.to_i32().wrapping_div(other.to_i32());
            Self::wrapping_from_i32(result)
        }
    }

    impl Rem = RemAssign rem_assign {
        fn rem(self, other) {
            let result = self.to_i32().wrapping_rem(other.to_i32());
            Self::wrapping_from_i32(result)
        }
    }


    impl BitAnd = BitAndAssign bitand_assign {
        fn bitand(self, rhs) {
            let bits = self.to_bits() & rhs.to_bits();
            // Safety:
            // since we and 2 values that both have the most significant byte set to zero
            // the output will always have the most significant byte set to zero
            unsafe { i24::from_bits(bits) }
        }
    }

    impl BitOr = BitOrAssign bitor_assign {
        fn bitor(self, rhs) {
            let bits = self.to_bits() | rhs.to_bits();
            // Safety:
            // since we and 2 values that both have the most significant byte set to zero
            // the output will always have the most significant byte set to zero
            unsafe { i24::from_bits(bits) }
        }
    }

    impl BitXor = BitXorAssign bitxor_assign {
        fn bitxor(self, rhs) {
            let bits = self.to_bits() ^ rhs.to_bits();
            // Safety:
            // since we and 2 values that both have the most significant byte set to zero
            // the output will always have the most significant byte set to zero
            unsafe { i24::from_bits(bits) }
        }
    }
}

impl Neg for i24 {
    type Output = Self;

    #[inline(always)]
    fn neg(self) -> Self {
        // this is how you negate twos compliment numbers
        i24::from_bits_truncate((!self.to_bits()) + 1)
    }
}

impl Not for i24 {
    type Output = Self;

    #[inline(always)]
    fn not(self) -> Self {
        i24::from_bits_truncate(!self.to_bits())
    }
}

impl Shl<u32> for i24 {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: u32) -> Self::Output {
        Self::from_bits_truncate(self.to_bits() << rhs)
    }
}

impl Shr<u32> for i24 {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: u32) -> Self::Output {
        // Safety:
        // we do a logical shift right by 8 at the end
        // and so the most significant octet/byte is set to 0

        // logic:
        // <8 bits empty> <i24 sign bit> <rest>
        // we shift everything up by 8
        // <i24 sign bit on i32 sign bit> <rest> <8 bits empty>
        // then we do an arithmetic shift
        // <sign bit * n> <i24 sign bit> <rest> <8 - n bits empty>
        // after we shift everything down by 8
        // <8 bits empty> <sign bit * n> <sign bit> <first 23 - n bits of rest>
        unsafe { Self::from_bits(((self.to_bits() << 8) as i32 >> rhs) as u32 >> 8) }
    }
}

impl ShrAssign<u32> for i24 {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: u32) {
        *self = Shr::shr(*self, rhs)
    }
}

impl ShlAssign<u32> for i24 {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: u32) {
        *self = Shl::shl(*self, rhs)
    }
}

macro_rules! impl_fmt {
    ($(impl $name: path)+) => {$(
        impl $name for i24 {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <i32 as $name>::fmt(&self.to_i32(), f)
            }
        }
    )*};
}

macro_rules! impl_bits_fmt {
    ($(impl $name: path)+) => {$(
        impl $name for i24 {
            #[inline(always)]
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

impl_bits_fmt! {
    impl UpperHex
    impl LowerHex

    impl Octal
    impl fmt::Binary
}

#[cfg(feature = "serde")]
mod serde {
    impl serde::Serialize for crate::i24 {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serializer.serialize_i32(self.to_i32())
        }
    }

    impl<'de> serde::Deserialize<'de> for crate::i24 {
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
                Ok(crate::i24::$from(v))
            }
        )*};
    }

    macro_rules! impl_deserialize_fallible {
        ($([$ty: path, $visit: ident, $try_from: ident])+) => {$(
            fn $visit<E>(self, v: $ty) -> Result<Self::Value, E> where E: serde::de::Error {
                crate::i24::$try_from(v).ok_or_else(|| E::custom("i24 out of range!"))
            }
        )*};
    }

    impl serde::de::Visitor<'_> for I24Visitor {
        type Value = crate::i24;

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

impl Hash for i24 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        I24Repr::hash(&self.0, state)
    }

    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
    where
        Self: Sized,
    {
        // i24 is repr(transparent)
        I24Repr::hash_slice(
            unsafe { core::mem::transmute::<&[Self], &[I24Repr]>(data) },
            state,
        )
    }
}

impl ToBytes for i24 {
    type Bytes = [u8; 3];

    fn to_be_bytes(&self) -> Self::Bytes {
        self.0.to_be_bytes()
    }

    fn to_le_bytes(&self) -> Self::Bytes {
        self.0.to_le_bytes()
    }
}

#[cfg(feature = "pyo3")]
#[pyclass(name = "I24")]
pub struct PyI24 {
    pub value: i24,
}

#[cfg(feature = "pyo3")]
#[pymodule(name = "i24")]
fn pyi24(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyI24>()?;
    Ok(())
}

#[cfg(feature = "pyo3")]
unsafe impl numpy::Element for i24 {
    const IS_COPY: bool = true;

    fn get_dtype_bound(py: Python<'_>) -> Bound<'_, numpy::PyArrayDescr> {
        numpy::dtype::<i24>(py)
    }

    fn clone_ref(&self, _py: Python<'_>) -> Self {
        self.clone()
    }

    fn get_dtype(py: Python<'_>) -> Bound<'_, PyArrayDescr> {
        numpy::dtype::<i24>(py)
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
        assert_eq!(i24::MAX.checked_add(i24::one()), None);
        assert_eq!(
            (i24::MAX - i24::one()).checked_add(i24::one() * i24!(2)),
            None
        );
    }

    #[test]
    fn test_checked_subtraction() {
        assert_eq!(i24!(10).checked_sub(i24!(20)), Some(i24!(-10)));
        assert_eq!(i24!(10).checked_sub(i24!(-20)), Some(i24!(30)));

        // Overflow cases
        assert_eq!(i24::MIN.checked_sub(i24::one()), None);
        assert_eq!(
            (i24::MIN + i24::one()).checked_sub(i24::one() * i24!(2)),
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
        assert_eq!(i24::MAX.checked_mul(i24!(2)), None);
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
            i24::from_ne_bytes([0x01, 0x02, 0x03]),
            if cfg!(target_endian = "big") { be } else { le }
        );
        assert_eq!(i24::from_le_bytes([0x01, 0x02, 0x03]), le);
        assert_eq!(i24::from_be_bytes([0x01, 0x02, 0x03]), be);
    }

    #[test]
    fn test_zero_and_one() {
        assert_eq!(i24::zero(), i24::try_from_i32(0).unwrap());

        assert_eq!(i24::zero(), i24!(0));
        assert_eq!(i24::one(), i24!(1));
    }

    #[test]
    fn test_from_str() {
        assert_eq!(i24::from_str("100").unwrap(), i24!(100));
        assert_eq!(i24::from_str("-100").unwrap(), i24!(-100));
        assert_eq!(i24::from_str(&format!("{}", i24::MAX)).unwrap(), i24::MAX);
        assert_eq!(i24::from_str(&format!("{}", i24::MIN)).unwrap(), i24::MIN);
        assert_eq!(
            *i24::from_str("8388608").unwrap_err().kind(),
            IntErrorKind::PosOverflow
        );
        assert_eq!(
            *i24::from_str("-8388609").unwrap_err().kind(),
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
        assert_eq!(i24::MAX + i24::one(), i24::MIN);
        assert_eq!(i24::MAX + i24::one() + i24::one(), i24::MIN + i24::one());

        assert_eq!(i24::MIN - i24::one(), i24::MAX);
        assert_eq!(i24::MIN - (i24::one() + i24::one()), i24::MAX - i24::one());

        assert_eq!(-i24::MIN, i24::MIN)
    }

    #[test]
    fn discriminant_optimization() {
        // this isn't guaranteed by rustc, but this should still hold true
        // if this fails because rustc stops doing it, just remove this test
        // otherwise investigate why this isn't working
        assert_eq!(size_of::<i24>(), size_of::<Option<i24>>());
        assert_eq!(size_of::<i24>(), size_of::<Option<Option<i24>>>());
        assert_eq!(size_of::<i24>(), size_of::<Option<Option<Option<i24>>>>());
        assert_eq!(
            size_of::<i24>(),
            size_of::<Option<Option<Option<Option<i24>>>>>()
        );
    }

    #[test]
    fn test_shift_operations() {
        let a = i24!(0b1);

        // Left shift
        assert_eq!(a << 23, i24::MIN); // 0x800000, which is the minimum negative value
        assert_eq!(a << 24, i24::zero()); // Shifts out all bits

        // Right shift
        let b = i24!(-1); // All bits set
        assert_eq!(b >> 1, i24!(-1)); // Sign extension
        assert_eq!(b >> 23, i24!(-1)); // Still all bits set due to sign extension
        assert_eq!(b >> 24, i24!(-1)); // No change after 23 bits

        // Edge case: maximum positive value
        let c = i24!(0x7FFFFF); // 8388607
        assert_eq!(c << 1, i24!(-2)); // 0xFFFFFE in 24-bit, which is -2 when sign-extended

        // Edge case: minimum negative value
        let d = i24::MIN; // (-0x800000)
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
            assert_eq!(i24::try_from_i32(i).unwrap().to_i32(), i)
        }
    }

    #[test]
    fn test_from() {
        macro_rules! impl_t {
            ($($ty: ty),+) => {{$(
                for x in <$ty>::MIN..=<$ty>::MAX {
                    assert_eq!(<$ty>::try_from(i24::from(x).to_i32()).unwrap(), x)
                }
            )+}};
        }

        assert_eq!(i24::from(true), i24::one());
        assert_eq!(i24::from(false), i24::zero());

        impl_t!(i8, i16, u8, u16)
    }

    #[test]
    fn test_try_from() {
        macro_rules! impl_t {
            (signed $($ty: ty),+) => {{$(
                for x in I24Repr::MIN..=I24Repr::MAX {
                    assert_eq!(i24::try_from(<$ty>::from(x)).unwrap().to_i32(), x)
                }
            )+}};

            (unsigned $($ty: ty),+) => {{$(
                for x in 0..=I24Repr::MAX {
                    assert_eq!(i24::try_from(<$ty>::try_from(x).unwrap()).unwrap().to_i32(), x)
                }
            )+}};
        }

        impl_t!(signed i32, i64, i128);
        impl_t!(unsigned u32, u64, u128);
    }

    #[test]
    fn test_to_from_bits() {
        for i in 0..(1 << 24) {
            assert_eq!(i24::from_bits_truncate(i).to_bits(), i)
        }
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_deserialize_json() {
        #[derive(Debug, PartialEq, ::serde::Deserialize)]
        struct TestStruct {
            value: i24,
        }

        let test: TestStruct =
            serde_json::from_str("{ \"value\": 11 }").expect("Failed to deserialize!");
        let expected = TestStruct {
            value: i24::from_u8(11),
        };

        assert_eq!(test, expected);
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_serialize_json() {
        #[derive(Debug, PartialEq, ::serde::Serialize)]
        struct TestStruct {
            value: i24,
        }

        let test_struct = TestStruct {
            value: i24::from_u8(11),
        };
        let test = serde_json::to_string(&test_struct).expect("Failed to serialize!");
        assert_eq!(test, "{\"value\":11}");
    }
}
