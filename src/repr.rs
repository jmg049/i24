use bytemuck::{NoUninit, Zeroable};
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub(crate) enum ZeroByte {
    Zero = 0,
}

const _: () =
    assert!(align_of::<u8>() == align_of::<ZeroByte>() && size_of::<u8>() == size_of::<ZeroByte>());

// Safety: ZeroByte is one single byte that is always initialized to zero
unsafe impl NoUninit for ZeroByte {}

// Safety: ZeroByte is one single byte that is always initialized to zero
// in fact the only valid bit pattern is zero
unsafe impl Zeroable for ZeroByte {}

#[cfg(feature = "alloc")]
/// Internal packed 3-byte representation of an [`crate::i24`] value used for zero-copy deserialization.
///
/// This struct is used internally in conjunction with [`bytemuck::cast_slice`] to reinterpret
/// `[u8]` data as a sequence of 24-bit signed integers.
///
/// # Safety
///
/// - It is `#[repr(C, packed)]` and consists of only `[u8; 3]`
/// - Implements `NoUninit` and `AnyBitPattern`, making it safe for binary reinterpretation
/// - Not exposed publicly — intended only for internal buffer conversions
#[repr(C, packed)]
#[derive(Copy, Clone)]
pub(crate) struct DiskI24 {
    pub(crate) bytes: [u8; 3],
}
#[cfg(feature = "alloc")]
/// Safety: all zeros is a valid value for DiskI24
unsafe impl bytemuck::Zeroable for DiskI24 {}
// Safety: No padding, all fields are u8s

#[cfg(feature = "alloc")]
/// Safety: DiskI24 is a packed struct with no padding
/// Any 3 bytes can be interpreted as a valid DiskI24
unsafe impl bytemuck::AnyBitPattern for DiskI24 {}

#[cfg(feature = "alloc")]
/// Safety: DiskI24 is a packed struct with no padding
/// Any 3 bytes can be interpreted as a valid DiskI24
unsafe impl bytemuck::NoUninit for DiskI24 {}

#[derive(Debug, Copy, Clone)]
#[repr(C, align(4))]
pub(super) struct BigEndianI24Repr {
    // most significant byte at the start
    pub(crate) most_significant_byte: ZeroByte,
    pub(crate) data: [u8; 3],
}

#[derive(Debug, Copy, Clone)]
#[repr(C, align(4))]
pub(super) struct LittleEndianI24Repr {
    pub(crate) data: [u8; 3],
    // most significant byte at the end
    pub(crate) most_significant_byte: ZeroByte,
}

#[cfg(target_endian = "big")]
pub(super) type I24Repr = BigEndianI24Repr;

#[cfg(target_endian = "little")]
pub(super) type I24Repr = LittleEndianI24Repr;

const _: () =
    assert!(align_of::<u32>() == align_of::<I24Repr>() && size_of::<u32>() == size_of::<I24Repr>());

// Safety: I24Repr is laid out in memory as a `u32` with the most significant byte set to zero
// Must be NoUninit due to the padding byte.
unsafe impl Zeroable for I24Repr {}

// Safety: I24 repr is laid out in memory as a `u32` with the most significant byte set to zero.
// Must be NoUninit due to the padding byte.
unsafe impl NoUninit for I24Repr {}

#[cfg(any(
    all(target_endian = "little", target_endian = "big"),
    not(any(target_endian = "little", target_endian = "big"))
))]
compile_error!("unknown endianness");

impl I24Repr {
    pub(super) const MAX: i32 = (1 << 23) - 1;
    pub(super) const MIN: i32 = -(1 << 23);
    pub(super) const BITS_MASK: u32 = 0xFFFFFF;

    #[inline]
    pub const fn to_i32(self) -> i32 {
        ((self.to_bits() as i32) << 8) >> 8
    }

    #[inline]
    pub const fn wrapping_from_i32(value: i32) -> Self {
        let proper_i24 = value as u32 & Self::BITS_MASK;

        // Safety: we only use the first 24 least significant bits (i.e 3 bytes) of the value,
        // and the most significant byte is set to zero
        // therefore layout guarantees hold true
        unsafe { Self::from_bits(proper_i24) }
    }

    #[inline]
    pub const fn saturating_from_i32(value: i32) -> Self {
        // Safety: we only use the first 24 least significant bits (i.e 3 bytes) of the value,
        // and the most significant byte is set to zero
        // therefore layout guarantees hold true
        if value > Self::MAX {
            const { Self::wrapping_from_i32(Self::MAX) }
        } else if value < Self::MIN {
            const { Self::wrapping_from_i32(Self::MIN) }
        } else {
            Self::wrapping_from_i32(value)
        }
    }

    #[inline(always)]
    pub const fn from_ne_bytes(bytes: [u8; 3]) -> Self {
        Self {
            data: bytes,
            most_significant_byte: ZeroByte::Zero,
        }
    }

    #[inline(always)]
    pub const fn from_be_bytes(bytes: [u8; 3]) -> Self {
        Self::from_ne_bytes(bytes).to_be()
    }

    #[inline(always)]
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        Self::from_ne_bytes(bytes).to_le()
    }

    pub const fn swap_bytes(self) -> Self {
        // can't just make a `swap_bytes` without endianness checks
        // because it also swaps their `repr`, and so this is easier to do
        #[cfg(target_endian = "little")]
        {
            self.to_be()
        }
        #[cfg(target_endian = "big")]
        {
            self.to_le()
        }
    }

    #[inline(always)]
    pub const fn to_be(self) -> Self {
        #[cfg(target_endian = "big")]
        {
            self
        }

        #[cfg(target_endian = "little")]
        {
            Self::from_ne_bytes(self.to_be_repr().data)
        }
    }

    #[inline(always)]
    pub const fn to_le(self) -> Self {
        #[cfg(target_endian = "little")]
        {
            self
        }

        #[cfg(target_endian = "big")]
        {
            Self::from_ne_bytes(self.to_le_repr().data)
        }
    }

    #[inline(always)]
    pub const fn to_ne_bytes(self) -> [u8; 3] {
        self.data
    }

    #[inline(always)]
    pub const fn to_be_bytes(self) -> [u8; 3] {
        self.to_be_repr().data
    }

    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 3] {
        self.to_le_repr().data
    }

    #[inline]
    const fn to_be_repr(self) -> BigEndianI24Repr {
        #[cfg(target_endian = "big")]
        {
            self
        }

        #[cfg(target_endian = "little")]
        {
            let val = self.to_bits().swap_bytes();

            // Safety:
            // since this is little endian, the bytes started off being laid out as
            // [data1, data2, data3, zero]
            // so after swapping the bytes it turns into
            // [zero, data3, data2, data1]
            // which is the proper layout for `BigEndianI24Repr`
            unsafe { core::mem::transmute::<u32, BigEndianI24Repr>(val) }
        }
    }

    #[inline]
    const fn to_le_repr(self) -> LittleEndianI24Repr {
        #[cfg(target_endian = "little")]
        {
            self
        }

        #[cfg(target_endian = "big")]
        {
            let val = self.to_bits().swap_bytes();

            // Safety:
            // since this is big endian, the bytes started off being laid out as
            // [zero, data3, data2, data1]
            // so after swapping the bytes it turns into
            // [data1, data2, data3, zero]
            // which is the proper layout for `LittleEndianI24Repr`
            unsafe { std::mem::transmute::<u32, LittleEndianI24Repr>(val) }.data
        }
    }

    #[inline(always)]
    pub(super) const fn to_bits(self) -> u32 {
        // Safety: I24Repr has the same memory layout as a `u32`
        unsafe { core::mem::transmute::<Self, u32>(self) }
    }

    /// Safety: the most significant byte has to equal 0
    #[inline(always)]
    pub(super) const unsafe fn from_bits(bits: u32) -> Self {
        debug_assert!((bits & Self::BITS_MASK) == bits);
        // Safety: upheld by caller
        unsafe { core::mem::transmute::<u32, Self>(bits) }
    }

    #[inline(always)]
    pub(super) const fn as_bits(&self) -> &u32 {
        // Safety: I24Repr has the same memory layout and alignment as a `u32`
        unsafe { core::mem::transmute::<&Self, &u32>(self) }
    }

    /// this returns a slice of u32's with the most significant byte set to zero
    #[inline(always)]
    const fn slice_as_bits(slice: &[Self]) -> &[u32] {
        // Safety: I24Repr has the same memory layout and alignment as a `u32`
        unsafe { core::mem::transmute::<&[Self], &[u32]>(slice) }
    }

    #[inline(always)]
    const fn const_eq(&self, other: &Self) -> bool {
        (*self.as_bits()) == (*other.as_bits())
    }
}

macro_rules! impl_infallible_unsigned {
    ($($meth: ident: $ty:ty),+) => {$(
        impl I24Repr {
            #[inline(always)]
            pub const fn $meth(x: $ty) -> Self {
                const {
                    assert!(<$ty>::MIN == 0 && <$ty>::BITS < 24);
                }

                // checked by the assert above
                unsafe { Self::from_bits(x as u32) }
            }
        }
    )+};
}

trait BoolLimits {
    const MIN: u8 = 0;
    const BITS: u32 = 1;
}

impl BoolLimits for bool {}

impl_infallible_unsigned! {
    from_u8: u8,
    from_u16: u16,
    from_bool: bool
}

macro_rules! impl_infallible_signed {
    ($($meth: ident: $ty:ty),+) => {$(
        impl I24Repr {
            #[inline(always)]
            pub const fn $meth(x: $ty) -> Self {
                const {
                    assert!(<$ty>::MIN < 0 && <$ty>::BITS < 24);
                }

                // at least on x86 (and probably all arches with sign extention)
                // this seems like the implementation with the best code gen
                // https://rust.godbolt.org/z/eThE5n9s1 -> from_i16_3

                // `x as u32` sign extends in accord to the refrence (https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions)
                // if positive this would be just the exact same number
                // if negative the sign extention is done for us and all we have to do
                // is zero out the high byte
                unsafe { Self::from_bits(x as u32 & Self::BITS_MASK) }
            }
        }
    )+};
}

impl_infallible_signed! {
    from_i8: i8,
    from_i16: i16
}

macro_rules! impl_fallible_unsigned {
    ($($meth: ident: $ty:ty),+) => {$(
        impl I24Repr {
            #[inline(always)]
            pub const fn $meth(x: $ty) -> Option<Self> {
                const { assert!(<$ty>::MIN == 0 && <$ty>::BITS > 24) }

                // the 2 impls have equivlent codegen
                // https://rust.godbolt.org/z/nE7nzGKPT
                if x > const { Self::MAX as $ty } {
                    return None
                }

                // Safety: x is <= Self::MAX meaning the msb is 0
                Some(unsafe { Self::from_bits(x as u32) })
            }
        }
    )+};
}

impl_fallible_unsigned! {
    try_from_u32: u32,
    try_from_u64: u64,
    try_from_u128: u128
}

macro_rules! impl_fallible_signed {
    ($($meth: ident: $ty:ty),+) => {$(
        impl I24Repr {
            #[inline(always)]
            pub const fn $meth(x: $ty) -> Option<Self> {
                const { assert!(<$ty>::MIN < 0 && <$ty>::BITS > 24) }

                if x < const { Self::MIN as $ty } || x > const { Self::MAX as $ty } {
                    return None
                }


                // this cast already sign extends as the source is signed
                // so we get a valid twos compliment number

                // Safety: we zero off the msb
                Some(unsafe { Self::from_bits(x as u32 & Self::BITS_MASK) })
            }
        }
    )+};
}

impl_fallible_signed! {
    try_from_i32: i32,
    try_from_i64: i64,
    try_from_i128: i128
}

impl PartialOrd<Self> for I24Repr {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for I24Repr {
    fn cmp(&self, other: &Self) -> Ordering {
        <i32 as Ord>::cmp(&self.to_i32(), &other.to_i32())
    }
}

impl PartialEq<Self> for I24Repr {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        I24Repr::const_eq(self, other)
    }
}

impl Eq for I24Repr {}

impl Hash for I24Repr {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        u32::hash(self.as_bits(), state)
    }

    #[inline(always)]
    fn hash_slice<H: Hasher>(data: &[Self], state: &mut H)
    where
        Self: Sized,
    {
        u32::hash_slice(I24Repr::slice_as_bits(data), state)
    }
}

impl Default for I24Repr {
    fn default() -> Self {
        I24Repr::zeroed()
    }
}

const _: () = {
    macro_rules! unwrap {
        ($e: expr) => {
            match $e {
                Some(x) => x,
                None => panic!("`unwrap` failed"),
            }
        };
    }

    // test arbitrary numbers
    assert!(I24Repr::const_eq(
        &unwrap!(I24Repr::try_from_i32(
            unwrap!(I24Repr::try_from_i32(349)).to_i32() - 1897
        )),
        &unwrap!(I24Repr::try_from_i32(349 - 1897))
    ));

    // test MIN
    assert!(unwrap!(I24Repr::try_from_i32(I24Repr::MIN)).to_i32() == I24Repr::MIN);

    // test MIN
    assert!(unwrap!(I24Repr::try_from_i32(I24Repr::MAX)).to_i32() == I24Repr::MAX);
};

const _: () = {
    // ZeroByte layout checks
    assert!(size_of::<ZeroByte>() == 1, "ZeroByte should be 1 byte");
    assert!(
        align_of::<ZeroByte>() == 1,
        "ZeroByte should have alignment 1"
    );

    // BigEndianI24Repr layout checks
    assert!(
        size_of::<BigEndianI24Repr>() == 4,
        "BigEndianI24Repr should be 4 bytes"
    );
    assert!(
        align_of::<BigEndianI24Repr>() == 4,
        "BigEndianI24Repr should be aligned to 4"
    );

    // LittleEndianI24Repr layout checks
    assert!(
        size_of::<LittleEndianI24Repr>() == 4,
        "LittleEndianI24Repr should be 4 bytes"
    );
    assert!(
        align_of::<LittleEndianI24Repr>() == 4,
        "LittleEndianI24Repr should be aligned to 4"
    );

    // I24Repr layout check (resolved depending on target endianness)
    assert!(size_of::<I24Repr>() == 4, "I24Repr should be 4 bytes");
    assert!(align_of::<I24Repr>() == 4, "I24Repr should be aligned to 4");
};
