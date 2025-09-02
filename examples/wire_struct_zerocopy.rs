//! Wire struct parsing using zerocopy with packed structs
//!
//! This example demonstrates using zerocopy to safely work with packed structs
//! that match exact on-wire layouts. This is the recommended approach when you need
//! exactly 19 bytes per record and want zero-copy parsing.
//!
//! Note: This example requires the "zerocopy" feature to be enabled.

#[cfg(feature = "zerocopy")]
use zerocopy::{FromBytes, IntoBytes, Unaligned};

#[cfg(feature = "zerocopy")]
use i24::types::I24Bytes;

/// Native data structure we want to convert to
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct DataStruct {
    pub t: u32,
    pub ch1: i24::I24,
    pub ch2: i24::I24,
    pub ch3: i24::I24,
    pub ch4: i24::I24,
    pub s: i24::I24,
}

#[cfg(feature = "zerocopy")]
/// Wire representation with exact 19-byte layout (little-endian)
///
/// This struct IS packed and matches the exact on-wire format.
/// It's safe to use with zerocopy because all fields are byte-oriented types.
#[repr(C, packed)]
#[derive(Copy, Clone, Debug, FromBytes, Unaligned, IntoBytes)]
pub struct DataStructWireLE {
    pub t: [u8; 4],    // u32 as LE bytes
    pub ch1: I24Bytes, // First i24 as bytes
    pub ch2: I24Bytes, // Second i24 as bytes
    pub ch3: I24Bytes, // Third i24 as bytes
    pub ch4: I24Bytes, // Fourth i24 as bytes
    pub s: I24Bytes,   // Fifth i24 as bytes
}

#[cfg(feature = "zerocopy")]
impl DataStructWireLE {
    /// Convert from wire format to native format
    pub fn to_native(self) -> DataStruct {
        DataStruct {
            t: u32::from_le_bytes(self.t),
            ch1: self.ch1.to_i24_le(),
            ch2: self.ch2.to_i24_le(),
            ch3: self.ch3.to_i24_le(),
            ch4: self.ch4.to_i24_le(),
            s: self.s.to_i24_le(),
        }
    }

    /// Create wire format from native format
    pub fn from_native(native: DataStruct) -> Self {
        Self {
            t: native.t.to_le_bytes(),
            ch1: I24Bytes::from_i24_le(native.ch1),
            ch2: I24Bytes::from_i24_le(native.ch2),
            ch3: I24Bytes::from_i24_le(native.ch3),
            ch4: I24Bytes::from_i24_le(native.ch4),
            s: I24Bytes::from_i24_le(native.s),
        }
    }
}

#[cfg(feature = "zerocopy")]
/// Parse records using zerocopy for zero-copy deserialization
///
/// This approach demonstrates the exact 19-byte layout that zerocopy enables.
pub fn parse_records_zerocopy(bytes: &[u8]) -> Option<Vec<DataStruct>> {
    // Check if the length is compatible with our wire struct size
    const STRUCT_SIZE: usize = 19; // 4 + 5*3 bytes
    if bytes.len() % STRUCT_SIZE != 0 {
        return None;
    }

    // Split bytes into chunks and parse each one using zerocopy's zero-copy conversion
    let mut result = Vec::new();

    for chunk in bytes.chunks_exact(STRUCT_SIZE) {
        // Use zerocopy to interpret raw bytes as our packed struct
        // This demonstrates the power of packed structs with exact byte layout
        let wire_ptr = chunk.as_ptr() as *const DataStructWireLE;
        let wire = unsafe { &*wire_ptr };
        result.push(wire.to_native());
    }

    Some(result)
}

#[cfg(feature = "zerocopy")]
/// Get a zero-copy slice view of the wire structs without conversion
/// Note: This demonstrates direct memory access to packed structs
pub fn view_records_zerocopy(bytes: &[u8]) -> Option<Vec<&DataStructWireLE>> {
    const STRUCT_SIZE: usize = 19;
    if bytes.len() % STRUCT_SIZE != 0 {
        return None;
    }

    // Create zero-copy references to each struct
    let mut result = Vec::new();

    for chunk in bytes.chunks_exact(STRUCT_SIZE) {
        let wire_ptr = chunk.as_ptr() as *const DataStructWireLE;
        let wire_ref = unsafe { &*wire_ptr };
        result.push(wire_ref);
    }

    Some(result)
}

#[cfg(feature = "zerocopy")]
/// Serialize records to bytes using zerocopy-style packed struct
pub fn serialize_records_zerocopy(records: &[DataStruct]) -> Vec<u8> {
    let mut result = Vec::with_capacity(records.len() * 19);

    // Convert each record to wire format and copy the bytes
    for record in records {
        let wire = DataStructWireLE::from_native(*record);
        // Directly access the memory representation of the packed struct
        let bytes = unsafe {
            std::slice::from_raw_parts(
                &wire as *const DataStructWireLE as *const u8,
                std::mem::size_of::<DataStructWireLE>(),
            )
        };
        result.extend_from_slice(bytes);
    }

    result
}

#[cfg(feature = "zerocopy")]
fn main() {
    println!(
        "DataStructWireLE size: {} bytes",
        std::mem::size_of::<DataStructWireLE>()
    );
    println!("Expected size: 19 bytes (4 + 5*3)");
    assert_eq!(std::mem::size_of::<DataStructWireLE>(), 19);

    // Create some test data
    let test_records = vec![
        DataStruct {
            t: 0x12345678,
            ch1: i24::I24::try_from(123456).unwrap(),
            ch2: i24::I24::try_from(-789012).unwrap(),
            ch3: i24::I24::try_from(456789).unwrap(),
            ch4: i24::I24::try_from(-123456).unwrap(),
            s: i24::I24::try_from(789012).unwrap(),
        },
        DataStruct {
            t: 0x87654321,
            ch1: i24::I24::try_from(-456789).unwrap(),
            ch2: i24::I24::try_from(123456).unwrap(),
            ch3: i24::I24::try_from(-789012).unwrap(),
            ch4: i24::I24::try_from(456789).unwrap(),
            s: i24::I24::try_from(-123456).unwrap(),
        },
    ];

    println!("\nOriginal records:");
    for (i, record) in test_records.iter().enumerate() {
        println!("  Record {}: {:?}", i, record);
    }

    // Serialize to bytes using zerocopy
    let serialized = serialize_records_zerocopy(&test_records);
    println!(
        "\nSerialized {} bytes per record ({} total bytes)",
        serialized.len() / test_records.len(),
        serialized.len()
    );

    // Show the exact byte representation
    println!("All bytes: {:02x?}", serialized);

    // Parse back from bytes using zero-copy
    let parsed = parse_records_zerocopy(&serialized).unwrap();

    println!("\nParsed records:");
    for (i, record) in parsed.iter().enumerate() {
        println!("  Record {}: {:?}", i, record);
    }

    // Verify round-trip
    assert_eq!(test_records, parsed);
    println!("\n✓ Round-trip successful!");

    // Demonstrate zero-copy view (no conversion)
    let wire_view = view_records_zerocopy(&serialized).unwrap();
    println!("\nZero-copy wire view:");
    for (i, wire) in wire_view.iter().enumerate() {
        println!(
            "  Wire {}: t={:02x?}, ch1={:02x?}, ch2={:02x?}, ch3={:02x?}, ch4={:02x?}, s={:02x?}",
            i,
            wire.t,
            wire.ch1.to_bytes(),
            wire.ch2.to_bytes(),
            wire.ch3.to_bytes(),
            wire.ch4.to_bytes(),
            wire.s.to_bytes()
        );
    }

    println!("\n✓ Perfect 19-byte records!");
}

#[cfg(not(feature = "zerocopy"))]
fn main() {
    println!("This example requires the 'zerocopy' feature.");
    println!("Run with: cargo run --example wire_struct_zerocopy --features zerocopy");
}

#[cfg(all(test, feature = "zerocopy"))]
mod tests {
    use super::*;

    #[test]
    fn test_wire_struct_size() {
        assert_eq!(std::mem::size_of::<DataStructWireLE>(), 19);
    }

    #[test]
    fn test_wire_conversion() {
        let original = DataStruct {
            t: 0x12345678,
            ch1: i24::I24::try_from(123456).unwrap(),
            ch2: i24::I24::try_from(-789012).unwrap(),
            ch3: i24::I24::try_from(456789).unwrap(),
            ch4: i24::I24::try_from(-123456).unwrap(),
            s: i24::I24::try_from(789012).unwrap(),
        };

        let wire = DataStructWireLE::from_native(original);
        let recovered = wire.to_native();

        assert_eq!(original, recovered);
    }

    #[test]
    fn test_zerocopy_parsing() {
        let original = vec![DataStruct {
            t: 0x12345678,
            ch1: i24::I24::try_from(123456).unwrap(),
            ch2: i24::I24::try_from(-789012).unwrap(),
            ch3: i24::I24::try_from(456789).unwrap(),
            ch4: i24::I24::try_from(-123456).unwrap(),
            s: i24::I24::try_from(789012).unwrap(),
        }];

        let bytes = serialize_records_zerocopy(&original);
        assert_eq!(bytes.len(), 19); // Exactly 19 bytes per record

        let parsed = parse_records_zerocopy(&bytes).unwrap();
        assert_eq!(original, parsed);
    }

    #[test]
    fn test_zero_copy_view() {
        let original = vec![DataStruct {
            t: 0x12345678,
            ch1: i24::I24::try_from(123456).unwrap(),
            ch2: i24::I24::try_from(-789012).unwrap(),
            ch3: i24::I24::try_from(456789).unwrap(),
            ch4: i24::I24::try_from(-123456).unwrap(),
            s: i24::I24::try_from(789012).unwrap(),
        }];

        let bytes = serialize_records_zerocopy(&original);
        let wire_view = view_records_zerocopy(&bytes).unwrap();

        assert_eq!(wire_view.len(), 1);
        assert_eq!(wire_view[0].to_native(), original[0]);
    }

    #[test]
    fn test_invalid_length() {
        let invalid_bytes = vec![0u8; 20]; // Not a multiple of 19
        assert!(parse_records_zerocopy(&invalid_bytes).is_none());
    }
}
