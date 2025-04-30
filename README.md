<div align="center">

# i24: A 24-bit Signed Integer Type for Rust

<img src="logo.png" alt="i24 Logo" width="200"/>

[![Crates.io](https://img.shields.io/crates/v/i24.svg)](https://crates.io/crates/i24)[![Docs.rs](https://docs.rs/i24/badge.svg)](https://docs.rs/i24)![MSRV: 1.70+](https://img.shields.io/badge/MSRV-1.70+-blue)
</div>

The ``i24`` crate provides a 24-bit signed integer type for Rust, filling the gap between
``i16`` and ``i32``. This type is particularly useful in audio processing, certain embedded
 systems, and other scenarios where 24-bit precision is required but 32 bits would be excessive.

## Features

- Efficient 24-bit signed integer representation
- Seamless conversion to and from ``i32``
- Support for basic arithmetic operations with overflow checking
- Bitwise operations
- Conversions from various byte representations (little-endian, big-endian, native)
- Implements common traits like``Debug``,``Display``,``PartialEq``,``Eq``,``PartialOrd``,``Ord``, and``Hash``

 This crate came about as a part of the [Wavers](https://crates.io/crates/wavers) project, which is a Wav file reader and writer for Rust.
 The ``i24`` struct also has pyo3 bindings for use in Python. Enable the``pyo3`` feature to use the pyo3 bindings.

## Usage

 Add this to your`` Cargo.toml`:

````toml
 [dependencies]
 i24 = "2.1.0"
````

 Then, in your Rust code:

````rust

# #[macro_use] extern crate i24

 let a = i24!(1000);
 let b = i24!(2000);
 let c = a + b;
 assert_eq!(c.to_i32(), 3000);
 assert_eq!(c, i24!(3000));
````

 The``i24!`` macro allows you to create``i24`` values at compile time, ensuring that the value is within the valid range.

 Then if working with 3-byte representations from disk or the network, you can use the``I24DiskMethods`` trait to read and write ``i24`` slices of ``i24`.

 ````ignore
 use i24::I24DiskMethods; // Bring extension trait into scope
 use i24::i24 as I24; // Import the i24 type
 let raw_data: &[u8] = &[0x00, 0x01, 0x02, 0x00, 0x01, 0xFF]; // 2 values
 let values: Vec<I24> = I24::read_i24s_be(raw_data).expect("valid buffer");

 let encoded: Vec<u8> = I24::write_i24s_be(&values);
 assert_eq!(encoded, raw_data);
````

## Safety and Limitations

 While``i24`` strives to behave similarly to Rust's built-in integer types, there are some
 important considerations:

- The valid range for ``i24`` is [-8,388,608, 8,388,607].
- Overflow behavior in arithmetic operations matches that of ``i32`.
- Bitwise operations are performed on the 24-bit representation.

Always use checked arithmetic operations when dealing with untrusted input or when
overflow/underflow is a concern.

``i24`` aligns with the safety requirements of bytemuck (``NoUninit``, ``Zeroable`` and ``AnyBitPattern``), ensuring that it is safe to use for converting between valid bytes and a ``i24`` value.
Then when using the ``I24DiskMethods`` trait, it is safe to use (internally) the ``bytemuck::cast_slice`` function to convert between a slice of bytes and a slice of ``i24`` values.

## Feature Flags

- **pyo3**: Enables the pyo3 bindings for the ``i24`` type.
- **serde**: Enables the ``Serialize`` and ``Deserialize`` traits for the ``i24`` type.
- **alloc**: Enables the ``I24DiskMethods`` trait for the ``i24`` type.

## Contributing

 Contributions are welcome! Please feel free to submit a Pull Request.

## License

 This project is licensed under MIT - see the [LICENSE](https://github.com/jmg049/i24/blob/main/LICENSE) file for details.

## Benchmarks

The crate was tested using the code found in the [i24_benches](./i24_benches) directory of the repo. The full benchmark data can be found in the [benchmark report](./i24_benches/benchmark_analysis/benchmark_report.md).
Below is a figure which summarises the performance with repsect to the ``i32`` type. From the figure it is clear that the ``i24`` type mostly matches the performance of an ``i32`` with some slight variations.

![Durations overview per operation](i24_benches/benchmark_analysis/operation_durations.png)

## Related Projects

This crate was developed as part of the [Wavers](https://crates.io/crates/wavers) project, a Wav file reader and writer for Rust.
