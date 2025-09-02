//! Wire struct parsing using bytemuck with non-packed structs
//!
//! This example demonstrates using bytemuck to cast byte slices directly to structs,
//! but avoiding packed structs to maintain Pod safety. This approach is safe but
//! may introduce padding that doesn't match the on-wire format exactly.
//!
//! For the exact 19-byte format from the issue, this approach requires the wire format
//! to have matching padding, or you should use the chunking or zerocopy approaches instead.

// Pod and Zeroable are not directly used but are traits implemented by I24Bytes
use i24::types::I24Bytes;

/// Wire representation using byte types (safe for bytemuck::Pod)
///
/// This struct is NOT packed, so Rust may add padding for alignment.
/// The layout will be: [4 bytes u32][3 bytes I24Bytes][1 byte padding]?[3 bytes I24Bytes][1 byte padding]?...
/// This matches the wire format only if the wire format also has this padding.
#[repr(C)]
#[derive(Copy, Clone, Debug, bytemuck::Pod, bytemuck::Zeroable)]
pub struct DataStructWire {
    pub t_bytes: [u8; 4], // u32 as bytes
    pub ch1: I24Bytes,    // First i24
    pub ch2: I24Bytes,    // Second i24
    pub ch3: I24Bytes,    // Third i24
    pub ch4: I24Bytes,    // Fourth i24
    pub s: I24Bytes,      // Fifth i24
}

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

impl DataStructWire {
    /// Convert from wire format to native format (little-endian interpretation)
    pub fn to_native_le(self) -> DataStruct {
        DataStruct {
            t: u32::from_le_bytes(self.t_bytes),
            ch1: self.ch1.to_i24_le(),
            ch2: self.ch2.to_i24_le(),
            ch3: self.ch3.to_i24_le(),
            ch4: self.ch4.to_i24_le(),
            s: self.s.to_i24_le(),
        }
    }

    /// Create wire format from native format (little-endian serialization)
    pub fn from_native_le(native: DataStruct) -> Self {
        Self {
            t_bytes: native.t.to_le_bytes(),
            ch1: I24Bytes::from_i24_le(native.ch1),
            ch2: I24Bytes::from_i24_le(native.ch2),
            ch3: I24Bytes::from_i24_le(native.ch3),
            ch4: I24Bytes::from_i24_le(native.ch4),
            s: I24Bytes::from_i24_le(native.s),
        }
    }
}

/// Parse records using bytemuck casting
///
/// IMPORTANT: This only works if the input byte stream has the same layout as DataStructWire,
/// including any padding that Rust adds for alignment.
pub fn parse_records_bytemuck(bytes: &[u8]) -> Option<Vec<DataStruct>> {
    // Check if the length is compatible with our wire struct size
    if bytes.len() % std::mem::size_of::<DataStructWire>() != 0 {
        return None;
    }

    // Cast the byte slice to wire structs
    let wire_structs: &[DataStructWire] = bytemuck::cast_slice(bytes);

    // Convert each wire struct to native format
    Some(wire_structs.iter().map(|w| w.to_native_le()).collect())
}

/// Serialize records using bytemuck casting
pub fn serialize_records_bytemuck(records: &[DataStruct]) -> Vec<u8> {
    // Convert to wire format
    let wire_structs: Vec<DataStructWire> = records
        .iter()
        .map(|r| DataStructWire::from_native_le(*r))
        .collect();

    // Cast to bytes
    bytemuck::cast_slice(&wire_structs).to_vec()
}

fn main() {
    println!(
        "DataStructWire size: {} bytes",
        std::mem::size_of::<DataStructWire>()
    );
    println!("I24Bytes size: {} bytes", std::mem::size_of::<I24Bytes>());
    println!(
        "I24Bytes alignment: {} bytes",
        std::mem::align_of::<I24Bytes>()
    );

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

    // Serialize to bytes using bytemuck
    let serialized = serialize_records_bytemuck(&test_records);
    println!(
        "\nSerialized {} bytes per record ({} total bytes)",
        serialized.len() / test_records.len(),
        serialized.len()
    );

    // Show a portion of the byte representation
    println!(
        "First 32 bytes: {:02x?}",
        &serialized[..32.min(serialized.len())]
    );

    // Parse back from bytes
    let parsed = parse_records_bytemuck(&serialized).unwrap();

    println!("\nParsed records:");
    for (i, record) in parsed.iter().enumerate() {
        println!("  Record {}: {:?}", i, record);
    }

    // Verify round-trip
    assert_eq!(test_records, parsed);
    println!("\n✓ Round-trip successful!");

    // Demonstrate the layout
    let wire = DataStructWire::from_native_le(test_records[0]);
    println!("\nWire struct layout demo:");
    println!("  t_bytes: {:02x?}", wire.t_bytes);
    println!("  ch1: {:02x?}", wire.ch1.to_bytes());
    println!("  ch2: {:02x?}", wire.ch2.to_bytes());
    println!("  ch3: {:02x?}", wire.ch3.to_bytes());
    println!("  ch4: {:02x?}", wire.ch4.to_bytes());
    println!("  s: {:02x?}", wire.s.to_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wire_struct_size() {
        // The wire struct should be at least 19 bytes (4 + 5*3)
        assert!(std::mem::size_of::<DataStructWire>() >= 19);
    }

    #[test]
    fn test_i24bytes_properties() {
        assert_eq!(std::mem::size_of::<I24Bytes>(), 3);
        assert_eq!(std::mem::align_of::<I24Bytes>(), 1);
    }

    #[test]
    fn test_bytemuck_cast() {
        let wire = DataStructWire {
            t_bytes: [0x78, 0x56, 0x34, 0x12], // 0x12345678 in LE
            ch1: I24Bytes([0x40, 0xE2, 0x01]), // 123456 in LE
            ch2: I24Bytes([0xEC, 0x23, 0xF4]), // -789012 in LE
            ch3: I24Bytes([0x15, 0xF8, 0x06]), // 456789 in LE
            ch4: I24Bytes([0xC0, 0x1D, 0xFE]), // -123456 in LE
            s: I24Bytes([0x14, 0xDC, 0x0B]),   // 789012 in LE
        };

        let bytes = bytemuck::bytes_of(&wire);
        let back: &DataStructWire = bytemuck::from_bytes(bytes);

        assert_eq!(wire.t_bytes, back.t_bytes);
        assert_eq!(wire.ch1, back.ch1);
    }

    #[test]
    fn test_round_trip() {
        let original = vec![DataStruct {
            t: 0x12345678,
            ch1: i24::I24::try_from(123456).unwrap(),
            ch2: i24::I24::try_from(-789012).unwrap(),
            ch3: i24::I24::try_from(456789).unwrap(),
            ch4: i24::I24::try_from(-123456).unwrap(),
            s: i24::I24::try_from(789012).unwrap(),
        }];

        let bytes = serialize_records_bytemuck(&original);
        let parsed = parse_records_bytemuck(&bytes).unwrap();

        assert_eq!(original, parsed);
    }
}
