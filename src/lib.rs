#![cfg_attr(not(feature = "std"), no_std)]
// Correctness and logic
#![warn(clippy::unit_cmp)] // Detects comparing unit types
#![warn(clippy::match_same_arms)] // Duplicate match arms

// Performance-focused
#![warn(clippy::inefficient_to_string)] // `format!("{}", x)` vs `x.to_string()`
#![warn(clippy::map_clone)] // Cloning inside `map()` unnecessarily
#![warn(clippy::unnecessary_to_owned)] // Detects redundant `.to_owned()` or `.clone()`
#![warn(clippy::large_stack_arrays)] // Helps avoid stack overflows
#![warn(clippy::box_collection)] // Warns on boxed `Vec`, `String`, etc.
#![warn(clippy::vec_box)] // Avoids using `Vec<Box<T>>` when unnecessary
#![warn(clippy::needless_collect)] // Avoids `.collect().iter()` chains

// Style and idiomatic Rust
#![warn(clippy::redundant_clone)] // Detects unnecessary `.clone()`
#![warn(clippy::identity_op)] // e.g., `x + 0`, `x * 1`
#![warn(clippy::needless_return)] // Avoids `return` at the end of functions
#![warn(clippy::let_unit_value)] // Avoids binding `()` to variables
#![warn(clippy::manual_map)] // Use `.map()` instead of manual `match`
#![warn(clippy::unwrap_used)] // Avoids using `unwrap()`
#![warn(clippy::panic)] // Avoids using `panic!` in production code

// Maintainability
#![warn(missing_docs)] // Warns on missing documentation. Everything should be documented!
#![warn(clippy::missing_panics_doc)] // Docs for functions that might panic
#![warn(clippy::missing_safety_doc)] // Docs for `unsafe` functions
#![warn(clippy::missing_const_for_fn)] // Suggests making eligible functions `const`

//! # i24: Integer Types for Rust (i24, u24)
//!
//! The `i24` crate provides specialized integer types for Rust: **i24** (24-bit signed) and **u24** (24-bit unsigned).
//! These types fill precision gaps in Rust's integer types
//! and are particularly useful in audio processing, embedded systems, network protocols, and other scenarios where
//! specific bit-width precision is required.
//!
//! ## Features
//!
//! ### Integer Types
//! - **i24**: 24-bit signed integer (range: -8,388,608 to 8,388,607)
//! - **u24**: 24-bit unsigned integer (range: 0 to 16,777,215)
//!
//! ### Core Functionality
//! - Seamless conversion to/from standard Rust integer types
//! - Complete arithmetic operations with overflow checking
//! - Bitwise operations
//! - Conversions from various byte representations (little-endian, big-endian, native)
//! - Wire/packed format support for binary protocols
//! - Compile-time macros: `i24!()` and `u24!()` for checked construction
//! - Implements standard traits: `Debug`, `Display`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`
//!
//! This crate came about as a part of the [Wavers](https://crates.io/crates/wavers) project, which is a Wav file reader and writer for Rust.
//! All integer types have Python bindings available via the `pyo3` feature.
//!
//! ## Usage
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! i24 = "2.2.0"
//! ```
//!
//! ### Basic Usage
//!
//! ```rust
//! use i24::{i24, u24};
//!
//! // Using macros for compile-time checked construction
//! let signed_24 = i24!(1000);
//! let unsigned_24 = u24!(2000);
//!
//! // Arithmetic operations
//! let sum_24 = signed_24 + i24!(500);
//! assert_eq!(sum_24.to_i32(), 1500);
//!
//! // Conversions
//! let as_i32: i32 = signed_24.into();
//! let as_u32: u32 = unsigned_24.into();
//! ```
//!
//! The `i24!()` and `u24!()` macros allow you to create values at compile time, ensuring they're within the valid range.
//!
//! ### Binary Data and Wire Formats
//!
//! For working with binary data, all types support reading/writing from byte arrays:
//!
//! ```rust
//! use i24::{I24, U24};
//!
//! // Reading from bytes (little-endian, big-endian, native)
//! let bytes_le = [0x00, 0x01, 0x02]; // 3-byte representation
//! let value = I24::from_le_bytes(bytes_le);
//!
//! // Writing to bytes
//! let bytes: [u8; 3] = value.to_be_bytes();
//!
//! // Bulk operations for slices
//! # #[cfg(feature = "alloc")]
//! # {
//! let raw_data: &[u8] = &[0x00, 0x01, 0x02, 0x00, 0x01, 0xFF];
//! let values: Vec<I24> = I24::read_i24s_be(raw_data).expect("valid buffer");
//! let encoded: Vec<u8> = I24::write_i24s_be(&values);
//! # }
//! ```
//!
//! ## Safety and Limitations
//!
//! All integer types strive to behave similarly to Rust's built-in integer types, with some important considerations:
//!
//! ### Value Ranges
//! - **i24**: [-8,388,608, 8,388,607]
//! - **u24**: [0, 16,777,215]  

//! ### Overflow Behavior
//! - Arithmetic operations match the behavior of their closest standard Rust integer type
//! - Bitwise operations are performed on the actual bit-width representation
//! - Always use checked arithmetic operations when dealing with untrusted input
//!
//! ### Memory Safety
//! All types align with `bytemuck` safety requirements (`NoUninit`, `Zeroable`, `AnyBitPattern`), ensuring safe byte-to-value conversions.
//! The bulk I/O operations use `bytemuck::cast_slice` internally for efficient, safe conversions.
//!
//! ## Feature Flags
//! - **pyo3**: Enables Python bindings for all integer types (i24, u24)
//! - **serde**: Enables `Serialize` and `Deserialize` traits for all integer types
//! - **alloc**: Enables bulk I/O operations and `PackedStruct` functionality
//! - **ndarray**: Enables `ScalarOperand` trait for use with ndarray operations
//! - **num-cast**: Enables `NumCast` trait implementations for safe numeric type conversion
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

pub mod types;
pub use types::{I24, I24Bytes, U24, U24Bytes};

pub(crate) mod repr;

#[doc(hidden)]
pub mod __macros__ {
    pub use bytemuck::Zeroable;
}

pub(crate) type TryFromIntError = <i8 as TryFrom<i64>>::Error;

#[allow(clippy::unwrap_used)] // Intentional use of unwrap
pub(crate) fn out_of_range() -> TryFromIntError {
    i8::try_from(i64::MIN).unwrap_err()
}

/// creates an `i24` from a constant expression
/// will give a compile error if the expression overflows an i24
#[macro_export]
macro_rules! i24 {
    (0) => {
        <I24 as $crate::__macros__::Zeroable>::zeroed()
    };
    ($e: expr) => {
        const {
            match $crate::I24::try_from_i32($e) {
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

/// creates an `u24` from a constant expression
/// will give a compile error if the expression overflows an u24
#[macro_export]
macro_rules! u24 {
    (0) => {
        <U24 as $crate::__macros__::Zeroable>::zeroed()
    };
    ($e: expr) => {
        const {
            match $crate::U24::try_from_u32($e) {
                Some(x) => x,
                None => panic!(concat!(
                    "out of range value ",
                    stringify!($e),
                    " used as an u24 constant"
                )),
            }
        }
    };
}

/// Helper utilities for working with packed structures containing `I24` values.
///
/// This module provides utilities to work around the limitation where Rust doesn't
/// allow nested `#[repr(packed)]` attributes. Since `I24` uses internal packing,
/// you cannot directly use `#[repr(packed, C)]` on structures containing `I24`.
///
/// These utilities provide safe alternatives for serializing and deserializing
/// mixed structures containing `I24` and native types.
#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use bytemuck::{Pod, try_cast_slice};

/// A trait for types that can be read from and written to packed byte representations.
///
/// This trait provides methods for handling structures that contain `I24` values
/// mixed with native types, working around the nested packing limitation.
pub trait PackedStruct: Sized {
    /// The size in bytes of the packed representation.
    const PACKED_SIZE: usize;

    /// Reads a single instance from packed bytes.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice containing the packed representation.
    ///   Must be at least `PACKED_SIZE` bytes long.
    ///
    /// # Returns
    ///
    /// The deserialized structure, or `None` if the input is too short.
    fn from_packed_bytes(bytes: &[u8]) -> Option<Self>;

    /// Writes the structure to a packed byte representation.
    ///
    /// # Returns
    ///
    /// A vector containing the packed bytes.
    #[cfg(feature = "alloc")]
    fn to_packed_bytes(&self) -> Vec<u8>;

    /// Reads multiple instances from a packed byte slice.
    ///
    /// # Arguments
    ///
    /// * `bytes` - A byte slice containing multiple packed structures.
    ///   Length must be a multiple of `PACKED_SIZE`.
    ///
    /// # Returns
    ///
    /// A vector of deserialized structures, or `None` if the input length
    /// is not a multiple of `PACKED_SIZE`.
    #[cfg(feature = "alloc")]
    fn from_packed_slice(bytes: &[u8]) -> Option<Vec<Self>> {
        if !bytes.len().is_multiple_of(Self::PACKED_SIZE) {
            return None;
        }

        let mut result = Vec::with_capacity(bytes.len() / Self::PACKED_SIZE);
        for chunk in bytes.chunks_exact(Self::PACKED_SIZE) {
            result.push(Self::from_packed_bytes(chunk)?);
        }
        Some(result)
    }

    /// Writes multiple structures to a packed byte representation.
    ///
    /// # Arguments
    ///
    /// * `structs` - A slice of structures to serialize.
    ///
    /// # Returns
    ///
    /// A vector containing all packed bytes concatenated.
    #[cfg(feature = "alloc")]
    fn to_packed_slice(structs: &[Self]) -> Vec<u8> {
        structs.iter().flat_map(|s| s.to_packed_bytes()).collect()
    }
}

/// Helper function to safely cast native types in mixed structures.
///
/// When you have a portion of your structure that contains only native types
/// (no I24), you can use this function to safely cast that portion using bytemuck.
///
/// # Arguments
///
/// * `bytes` - Byte slice containing the native types.
///
/// # Returns
///
/// A slice of the target type, or an error if the cast fails.
pub fn cast_native_slice<T: Pod>(bytes: &[u8]) -> Result<&[T], bytemuck::PodCastError> {
    try_cast_slice(bytes)
}

#[cfg(feature = "pyo3")]
pub use crate::types::{PyI24, PyU24};

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

#[cfg(feature = "pyo3")]
#[pymodule(name = "i24")]
fn pyi24(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyI24>()?;
    m.add_class::<PyU24>()?;
    Ok(())
}
