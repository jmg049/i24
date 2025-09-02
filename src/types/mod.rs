//! Integer type implementations for 24-bit signed and unsigned integers.
//!
//! This module contains the core `I24` and `U24` types along with their
//! associated byte array types `I24Bytes` and `U24Bytes`.

mod i24;
mod u24;

pub use i24::{I24, I24Bytes};
pub use u24::{U24, U24Bytes};

#[cfg(feature = "pyo3")]
pub use i24::python::PyI24;

#[cfg(feature = "pyo3")]
pub use u24::python::PyU24;
