i24: A 24-bit Signed Integer Type for Rust
i24 provides a 24-bit signed integer type for Rust, filling the gap between i16 and i32. This type is particularly useful in audio processing, certain embedded systems, and other scenarios where 24-bit precision is required but 32 bits would be excessive.
Features

Efficient 24-bit signed integer representation
Seamless conversion to and from i32
Support for basic arithmetic operations with overflow checking
Bitwise operations
Conversions from various byte representations (little-endian, big-endian, native)
Implements common traits like Debug, Display, PartialEq, Eq, PartialOrd, Ord, and Hash

Installation
Add this to your Cargo.toml:
toml