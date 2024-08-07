use bytemuck::{NoUninit, Zeroable};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
enum ZeroByte {
    Zero = 0,
}

const _: () =
    assert!(align_of::<u8>() == align_of::<ZeroByte>() && size_of::<u8>() == size_of::<ZeroByte>());

// Safety: ZeroByte is one single byte that is always initialized to zero
unsafe impl NoUninit for ZeroByte {}

// Safety: ZeroByte is one single byte that is always initialized to zero
// in fact the only valid bit pattern is zero
unsafe impl Zeroable for ZeroByte {}

#[derive(Debug, Copy, Clone)]
#[repr(C, align(4))]
pub(super) struct BigEndianI24Repr {
    // most significant byte at the start
    most_significant_byte: ZeroByte,
    data: [u8; 3],
}

#[derive(Debug, Copy, Clone)]
#[repr(C, align(4))]
pub(super) struct LittleEndianI24Repr {
    data: [u8; 3],
    // most significant byte at the end
    most_significant_byte: ZeroByte,
}

#[cfg(target_endian = "big")]
pub(super) type I24Repr = BigEndianI24Repr;

#[cfg(target_endian = "little")]
pub(super) type I24Repr = LittleEndianI24Repr;

const _: () =
    assert!(align_of::<u32>() == align_of::<I24Repr>() && size_of::<u32>() == size_of::<I24Repr>());

// Safety: I24Repr is laid out in memory as a `u32` with the most significant byte set to zero
unsafe impl NoUninit for I24Repr {}

// Safety: I24Repr is laid out in memory as a `u32` with the most significant byte set to zero
unsafe impl Zeroable for I24Repr {}

#[cfg(any(
    all(target_endian = "little", target_endian = "big"),
    not(any(target_endian = "little", target_endian = "big"))
))]
compile_error!("unknown endianness");

impl I24Repr {
    pub(super) const MAX: i32 = (1 << 23) - 1;
    pub(super) const MIN: i32 = -(1 << 23);

    pub(super) const SIGN_EXTEND: u32 = 0xFF000000;
    pub(super) const SIGN_BIT: u32 = 0x800000;
    pub(super) const BITS_MASK: u32 = 0xFFFFFF;

    #[inline]
    pub const fn to_i32(self) -> i32 {
        let mut value = self.to_bits();
        if value & Self::SIGN_BIT != 0 {
            value |= Self::SIGN_EXTEND
        }
        value as i32
    }

    #[inline]
    pub const fn wrapping_from_i32(value: i32) -> Self {
        let proper_i24 = (value as u32 & Self::BITS_MASK)
            | if value < 0 && value >= Self::MIN {
                Self::SIGN_BIT
            } else {
                0
            };

        debug_assert!((proper_i24 & Self::BITS_MASK) == proper_i24);

        // Safety: we only use the first 24 least significant bits (i.e 3 bytes) of the value,
        // and the most significant byte is set to zero
        // therefore layout guarantees hold true
        unsafe { I24Repr::from_bits(proper_i24) }
    }

    #[inline]
    pub const fn from_i32(value: i32) -> Option<Self> {
        // Check if value fits in the i24 range
        if value > Self::MAX || value < Self::MIN {
            return None;
        }

        Some(Self::wrapping_from_i32(value))
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

    pub const fn swap_bytes(self) -> I24Repr {
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
    pub const fn to_be(self) -> I24Repr {
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
    pub const fn to_le(self) -> I24Repr {
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
            unsafe { std::mem::transmute::<u32, BigEndianI24Repr>(val) }
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
        unsafe { std::mem::transmute::<I24Repr, u32>(self) }
    }

    /// Safety: the most significant byte has to equal 0
    #[inline(always)]
    pub(super) const unsafe fn from_bits(bits: u32) -> I24Repr {
        debug_assert!((bits & I24Repr::BITS_MASK) == bits);
        // Safety: upheld by caller
        unsafe { std::mem::transmute::<u32, I24Repr>(bits) }
    }

    #[inline(always)]
    pub(super) const fn as_bits(&self) -> &u32 {
        // Safety: I24Repr has the same memory layout and alignment as a `u32`
        unsafe { std::mem::transmute::<&I24Repr, &u32>(self) }
    }

    /// this returns a slice of u32's with the most significant byte set to zero
    #[inline(always)]
    const fn slice_as_bits(slice: &[Self]) -> &[u32] {
        // Safety: I24Repr has the same memory layout and alignment as a `u32`
        unsafe { std::mem::transmute::<&[I24Repr], &[u32]>(slice) }
    }

    #[inline(always)]
    const fn const_eq(&self, other: &Self) -> bool {
        (*self.as_bits()) == (*other.as_bits())
    }
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

const _ASSERTS: () = const {
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
        &unwrap!(I24Repr::from_i32(
            unwrap!(I24Repr::from_i32(349)).to_i32() - 1897
        )),
        &unwrap!(I24Repr::from_i32(349 - 1897))
    ));

    // test MIN
    assert!(unwrap!(I24Repr::from_i32(I24Repr::MIN)).to_i32() == I24Repr::MIN);

    // test MIN
    assert!(unwrap!(I24Repr::from_i32(I24Repr::MAX)).to_i32() == I24Repr::MAX);
};
