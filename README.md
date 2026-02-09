<div align="center">

# i24: Integer Types for Rust (i24, u24)

<img src="logo.png" alt="i24 Logo" width="200"/>

[![Crates.io][crate-img]][crate] [![Docs.rs][docs-img]][docs] [![PyPI][pypi-img]][pypi] [![PyDocs][docs-img-py]][docs-python] [![License: MIT][license-img]][license]

</div>

The ``i24`` crate provides specialized integer types for Rust: **i24** (24-bit signed) and **u24** (24-bit unsigned). These types fill precision gaps in Rust's integer types and are particularly useful in audio processing, embedded systems, network protocols, and other scenarios where specific bit-width precision is required.

## Features

### Integer Types

- **i24**: 24-bit signed integer (range: -8,388,608 to 8,388,607)
- **u24**: 24-bit unsigned integer (range: 0 to 16,777,215)

### Core Functionality

- Seamless conversion to/from standard Rust integer types
- Complete arithmetic operations with overflow checking
- Bitwise operations
- Conversions from various byte representations (little-endian, big-endian, native)
- Wire/packed format support for binary protocols
- Compile-time macros: ``i24!()`` and ``u24!()`` for checked construction
- Implements standard traits: ``Debug``, ``Display``, ``PartialEq``, ``Eq``, ``PartialOrd``, ``Ord``, ``Hash``

This crate came about as a part of the [Wavers](https://crates.io/crates/wavers) project, which is a Wav file reader and writer for Rust.
All integer types have Python bindings available via the ``pyo3`` feature.

## Usage

 Add this to your`` Cargo.toml`:

```toml
 [dependencies]
 i24 = "2.2.4"
```

or just run

```bash
cargo add i24
```

to get the latest version.

### Basic Usage

````rust
use i24::{i24, u24};

// Using macros for compile-time checked construction
let signed_24 = i24!(1000);
let unsigned_24 = u24!(2000);

// Arithmetic operations
let sum_24 = signed_24 + i24!(500);
assert_eq!(sum_24.to_i32(), 1500);

// Conversions
let as_i32: i32 = signed_24.into();
let as_u32: u32 = unsigned_24.into();
````

The ``i24!()`` and ``u24!()`` macros allow you to create values at compile time, ensuring they're within the valid range.

### Binary Data and Wire Formats

For working with binary data, all types support reading/writing from byte arrays:

````rust
use i24::{i24, u24};

// Reading from bytes (little-endian, big-endian, native)
let bytes_le = [0x00, 0x01, 0x02]; // 3-byte representation
let value = i24::from_le_bytes(bytes_le);

// Writing to bytes
let bytes: [u8; 3] = value.to_be_bytes();

// Bulk operations for slices
let raw_data: &[u8] = &[0x00, 0x01, 0x02, 0x00, 0x01, 0xFF];
let values: Vec<i24> = i24::read_i24s_be(raw_data).expect("valid buffer");
let encoded: Vec<u8> = i24::write_i24s_be(&values);
````

### Packed Structs

For binary protocols and serialization, use the ``PackedStruct`` trait:

````rust
use i24::{i24, packed::PackedStruct};

#[derive(Debug, Clone, PartialEq)]
struct WireFormat {
    header: u32,
    samples: [i24; 5],
}

impl PackedStruct for WireFormat {
    const PACKED_SIZE: usize = 4 + 5 * 3; // u32 + 5 * i24 = 19 bytes
    
    fn from_packed_bytes(bytes: &[u8]) -> Option<Self> {
        // Implementation for deserializing from bytes
        // ...
    }
    
    fn to_packed_bytes(&self) -> Vec<u8> {
        // Implementation for serializing to bytes
        // ...
    }
}
````

## Safety and Limitations

All integer types strive to behave similarly to Rust's built-in integer types, with some important considerations:

### Value Ranges

- **i24**: [-8,388,608, 8,388,607]
- **u24**: [0, 16,777,215]

### Overflow Behavior

- Arithmetic operations match the behavior of their closest standard Rust integer type
- Bitwise operations are performed on the actual bit-width representation
- Always use checked arithmetic operations when dealing with untrusted input

### Memory Safety

All types align with ``bytemuck`` safety requirements (``NoUninit``, ``Zeroable``, ``AnyBitPattern``), ensuring safe byte-to-value conversions. The bulk I/O operations use ``bytemuck::cast_slice`` internally for efficient, safe conversions.

## Feature Flags

- **pyo3**: Enables Python bindings for all integer types (i24, u24)
- **serde**: Enables ``Serialize`` and ``Deserialize`` traits for all integer types
- **alloc**: Enables bulk I/O operations and ``PackedStruct`` functionality

## Contributing

 Contributions are welcome! Please feel free to submit a Pull Request.

## License

 This project is licensed under MIT - see the [LICENSE](https://github.com/jmg049/i24/blob/main/LICENSE) file for details.

## Benchmarks

The crate was tested using the code found in the [i24_benches](./i24_benches) directory of the repo. Unsurprisingly, the performance of both types matches the performance of the underlying 32-bit type.

[crate]: https://crates.io/crates/i24
[crate-img]: https://img.shields.io/crates/v/i24?style=for-the-badge&color=009E73&label=crates.io

[docs]: https://docs.rs/i24
[docs-img]: https://img.shields.io/badge/docs.rs-online-009E73?style=for-the-badge&labelColor=gray

[license-img]: https://img.shields.io/crates/l/i24?style=for-the-badge&label=license&labelColor=gray  
[license]: https://github.com/jmg049/i24/blob/main/LICENSE

[pypi]: https://pypi.org/project/i24_type/
[pypi-img]: https://img.shields.io/pypi/v/i24_type?style=for-the-badge&color=009E73&label=PyPI

[docs-python]: https://jmg049.github.io/i24/
[docs-img-py]: https://img.shields.io/pypi/v/i24_type?style=for-the-badge&color=009E73&label=PyDocs