use bytemuck::{Pod, Zeroable};
use num_traits::{Num, One, Zero};
use std::fmt;
use std::fmt::Display;
use std::{
    ops::{Neg, Not},
    str::FromStr,
};

#[allow(non_camel_case_types)]
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[cfg_attr(feature = "pyo3", pyclass)]
/// An experimental 24-bit unsigned integer type.
///
/// This type is a wrapper around ``[u8; 3]`` and is used to represent 24-bit audio samples.
/// It should not be used anywhere important. It is still unverified and experimental.
///
/// The type is not yet fully implemented and is not guaranteed to work.
/// Supports basic arithmetic operations and conversions to and from ``i32``.
///
pub struct i24 {
    pub data: [u8; 3],
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
    type FromStrRadixErr = std::num::ParseIntError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        let i32_result = i32::from_str_radix(str, radix)?;
        Ok(i24::from_i32(i32_result))
    }
}

impl Display for i24 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_i32())
    }
}

impl FromStr for i24 {
    type Err = std::num::ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let i32_result = i32::from_str(s)?;
        Ok(i24::from_i32(i32_result))
    }
}

impl i24 {
    /// Returns the 24-bit integer as an i32.
    pub const fn to_i32(self) -> i32 {
        let [a, b, c] = self.data;
        i32::from_ne_bytes([a, b, c, 0])
    }

    /// Returns the i32 as a 24-bit integer.
    pub const fn from_i32(n: i32) -> Self {
        let [a, b, c, _d] = i32::to_ne_bytes(n);
        Self { data: [a, b, c] }
    }

    /// Creates a 24-bit integer from a array of 3 bytes in native endian format.
    pub const fn from_ne_bytes(bytes: [u8; 3]) -> Self {
        let i32_result = i32::from_ne_bytes([bytes[0], bytes[1], bytes[2], 0]);
        i24::from_i32(i32_result)
    }

    /// Creates a 24-bit integer from a array of 3 bytes in little endian format.
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        let i32_result = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], 0]);
        i24::from_i32(i32_result)
    }

    /// Creates a 24-bit integer from a array of 3 bytes in big endian format.
    pub const fn from_be_bytes(bytes: [u8; 3]) -> Self {
        let i32_result = i32::from_be_bytes([bytes[0], bytes[1], bytes[2], 0]);
        i24::from_i32(i32_result)
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
#[cfg(feature = "pyo3")]
use numpy::Element;

#[cfg(feature = "pyo3")]
unsafe impl Element for i24 {
    const IS_COPY: bool = true;

    fn get_dtype_bound(py: Python<'_>) -> Bound<'_, numpy::PyArrayDescr> {
        numpy::dtype_bound::<i24>(py)
    }
}

macro_rules! implement_ops {
    ($($trait_path:path { $($function_name:ident),* }),*) => {
        $(
            impl $trait_path for i24 {
                $(
                    type Output = Self;

                    fn $function_name(self, other: Self) -> Self {
                        let self_i32: i32 = self.to_i32();
                        let other_i32: i32 = other.to_i32();
                        let result = self_i32.$function_name(other_i32);
                        Self::from_i32(result)
                    }
                )*
            }
        )*
    };
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

implement_ops!(
    std::ops::Add { add },
    std::ops::Sub { sub },
    std::ops::Mul { mul },
    std::ops::Div { div },
    std::ops::Rem { rem },
    std::ops::BitAnd { bitand },
    std::ops::BitOr { bitor },
    std::ops::BitXor { bitxor },
    std::ops::Shl { shl },
    std::ops::Shr { shr }
);

implement_ops_assign!(
    std::ops::AddAssign { add_assign },
    std::ops::SubAssign { sub_assign },
    std::ops::MulAssign { mul_assign },
    std::ops::DivAssign { div_assign },
    std::ops::RemAssign { rem_assign },
    std::ops::BitAndAssign { bitand_assign },
    std::ops::BitOrAssign { bitor_assign },
    std::ops::BitXorAssign { bitxor_assign },
    std::ops::ShlAssign { shl_assign },
    std::ops::ShrAssign { shr_assign }
);

implement_ops_assign_ref!(
    std::ops::AddAssign { add_assign },
    std::ops::SubAssign { sub_assign },
    std::ops::MulAssign { mul_assign },
    std::ops::DivAssign { div_assign },
    std::ops::RemAssign { rem_assign },
    std::ops::BitAndAssign { bitand_assign },
    std::ops::BitOrAssign { bitor_assign },
    std::ops::BitXorAssign { bitxor_assign },
    std::ops::ShlAssign { shl_assign },
    std::ops::ShrAssign { shr_assign }
);
