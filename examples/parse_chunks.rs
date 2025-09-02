//! Manual 19-byte record parsing using chunking approach
//!
//! This example demonstrates parsing a binary stream containing records of mixed types:
//! - 1 u32 (4 bytes)
//! - 5 i24 values (15 bytes)
//!   Total: 19 bytes per record
//!
//! This approach manually chunks the byte stream and parses each field individually.
//! It works well when you need maximum control or when the wire format has padding
//! that doesn't match Rust struct alignment.

use i24::types::I24Bytes;

/// Native data structure we want to parse to
#[derive(Debug, PartialEq)]
pub struct DataStruct {
    pub t: u32,
    pub ch1: i24::I24,
    pub ch2: i24::I24,
    pub ch3: i24::I24,
    pub ch4: i24::I24,
    pub s: i24::I24,
}

/// Parse records from a byte stream using manual chunking (little-endian)
pub fn parse_records_le(bytes: &[u8]) -> Option<impl Iterator<Item = DataStruct> + '_> {
    const RECORD_SIZE: usize = 4 + 5 * 3; // 19 bytes per record

    // Ensure the input is evenly divisible into records
    if bytes.len() % RECORD_SIZE != 0 {
        return None;
    }

    let iterator = bytes.chunks_exact(RECORD_SIZE).map(|record| {
        // Parse u32 at offset 0-3
        let t = u32::from_le_bytes([record[0], record[1], record[2], record[3]]);

        // Helper to parse i24 at given offset
        let parse_i24 =
            |offset| I24Bytes([record[offset], record[offset + 1], record[offset + 2]]).to_i24_le();

        DataStruct {
            t,
            ch1: parse_i24(4),  // offset 4-6
            ch2: parse_i24(7),  // offset 7-9
            ch3: parse_i24(10), // offset 10-12
            ch4: parse_i24(13), // offset 13-15
            s: parse_i24(16),   // offset 16-18
        }
    });

    Some(iterator)
}

/// Serialize records back to bytes (little-endian)
pub fn serialize_records_le(records: &[DataStruct]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(records.len() * 19);

    for record in records {
        // Serialize u32
        bytes.extend_from_slice(&record.t.to_le_bytes());

        // Serialize each i24
        bytes.extend_from_slice(&I24Bytes::from_i24_le(record.ch1).to_bytes());
        bytes.extend_from_slice(&I24Bytes::from_i24_le(record.ch2).to_bytes());
        bytes.extend_from_slice(&I24Bytes::from_i24_le(record.ch3).to_bytes());
        bytes.extend_from_slice(&I24Bytes::from_i24_le(record.ch4).to_bytes());
        bytes.extend_from_slice(&I24Bytes::from_i24_le(record.s).to_bytes());
    }

    bytes
}

fn main() {
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

    println!("Original records:");
    for (i, record) in test_records.iter().enumerate() {
        println!("  Record {}: {:?}", i, record);
    }

    // Serialize to bytes
    let serialized = serialize_records_le(&test_records);
    println!(
        "\nSerialized {} bytes: {:02x?}",
        serialized.len(),
        &serialized[..20]
    );

    // Parse back from bytes
    let parsed: Vec<DataStruct> = parse_records_le(&serialized).unwrap().collect();

    println!("\nParsed records:");
    for (i, record) in parsed.iter().enumerate() {
        println!("  Record {}: {:?}", i, record);
    }

    // Verify round-trip
    assert_eq!(test_records, parsed);
    println!("\n✓ Round-trip successful!");

    // Demonstrate error handling
    let invalid_bytes = vec![0u8; 20]; // Not divisible by 19
    match parse_records_le(&invalid_bytes) {
        Some(_) => println!("\nUnexpected: should have failed"),
        None => println!("\n✓ Correctly rejected invalid input length"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        let bytes = serialize_records_le(&original);
        let parsed: Vec<_> = parse_records_le(&bytes).unwrap().collect();

        assert_eq!(original, parsed);
    }

    #[test]
    fn test_invalid_length() {
        let invalid_bytes = vec![0u8; 20]; // Not divisible by 19
        assert!(parse_records_le(&invalid_bytes).is_none());
    }

    #[test]
    fn test_empty_input() {
        let empty_bytes = &[];
        let parsed: Vec<_> = parse_records_le(empty_bytes).unwrap().collect();
        assert_eq!(parsed.len(), 0);
    }
}
