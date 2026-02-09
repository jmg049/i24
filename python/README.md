<div align="center">

# i24: Integer Types for Rust (i24, u24)

<img src="../logo.png" alt="i24 Logo" width="200"/>

[![Crates.io][crate-img]][crate] [![Docs.rs][docs-img]][docs] [![PyPI][pypi-img]][pypi] [![PyDocs][docs-img-py]][docs-python] [![License: MIT][license-img]][license]

</div>
The `i24` package provides specialized 24-bit integer types for Python: **I24** (signed) and **U24** (unsigned). These types are implemented in Rust for high performance and provide a Python interface for working with 24-bit integers commonly found in audio processing, embedded systems, network protocols, and binary data formats.

## Features

### Integer Types

- **I24**: 24-bit signed integer (range: -8,388,608 to 8,388,607)
- **U24**: 24-bit unsigned integer (range: 0 to 16,777,215)

### Core Functionality

- Full arithmetic and bitwise operations with overflow checking
- Conversion to/from Python `int` and `bytes`
- Little-endian, big-endian, and native byte order support
- NumPy integration for array operations
- Immutable (frozen) types for thread safety
- High performance Rust implementation
- Checked arithmetic operations (return `None` on overflow)
- Complete set of comparison operators

This package is part of the [i24](https://github.com/jmg049/i24) project, which also provides Rust implementations. The Python bindings were created to support the [Wavers](https://crates.io/crates/wavers) audio processing library.

## Installation

### Requirements

- Python 3.10 or later
- NumPy 1.26 or later (automatically installed as a dependency)

### From PyPI

```bash
pip install i24
```

### Upgrading

```bash
pip install --upgrade i24
```

### From Source

For development or to use the latest unreleased features:

```bash
git clone https://github.com/jmg049/i24.git
cd i24
pip install maturin
maturin develop --release
```

## Quick Start

### Basic Usage

```python
from i24 import I24, U24

# Create 24-bit integers
signed = I24(1000)
unsigned = U24(2000)

# Arithmetic operations
result = signed + I24(500)
print(result.to_int())  # 1500

# Conversions
as_int = int(signed)
print(as_int)  # 1000
```

### Working with Bytes

```python
from i24 import I24, U24

# Create from bytes (little-endian)
bytes_le = bytes([0x00, 0x10, 0x00])
value = I24.from_bytes(bytes_le, byteorder='little')
print(value.to_int())  # 4096

# Convert to bytes (big-endian)
be_bytes = value.to_bytes(byteorder='big')
print(be_bytes)  # b'\x00\x10\x00'

# Create from big-endian bytes
bytes_be = bytes([0x12, 0x34, 0x56])
value = I24.from_bytes(bytes_be, byteorder='big')
print(hex(value.to_int()))  # 0x123456
```

### Checked Arithmetic

Checked arithmetic methods return `None` on overflow instead of raising exceptions:

```python
from i24 import I24

a = I24(8_000_000)
b = I24(500_000)

# Safe addition
result = a.checked_add(b)
if result is None:
    print("Addition would overflow")
else:
    print(f"Result: {result.to_int()}")

# Other checked operations
result = a.checked_sub(b)  # Checked subtraction
result = a.checked_mul(I24(2))  # Checked multiplication
result = a.checked_div(b)  # Checked division (also checks for division by zero)
```

## Value Ranges and Overflow Behavior

### Value Ranges

- **I24**: [-8,388,608, 8,388,607]
- **U24**: [0, 16,777,215]

### Overflow Behavior

Standard operators raise `OverflowError` when results exceed the valid range:

```python
from i24 import I24

a = I24(8_000_000)
b = I24(500_000)

try:
    result = a + b  # This will overflow
except OverflowError as e:
    print(f"Overflow: {e}")
```

Use checked arithmetic methods when you want to handle overflow explicitly without exceptions.

### Division by Zero

Division operations raise `ZeroDivisionError`:

```python
from i24 import I24

a = I24(1000)
zero = I24(0)

try:
    result = a / zero
except ZeroDivisionError as e:
    print(f"Error: {e}")
```

## Supported Operations

### Arithmetic Operations

```python
from i24 import I24, U24

a = I24(1000)
b = I24(500)

# Standard operators
sum_val = a + b       # Addition
diff = a - b          # Subtraction
prod = a * b          # Multiplication
quot = a / b          # Division (returns float)
floor_div = a // b    # Floor division
mod = a % b           # Modulo
neg = -a              # Negation
pos = +a              # Unary plus

# Checked operations (return None on overflow)
safe_sum = a.checked_add(b)
safe_diff = a.checked_sub(b)
safe_prod = a.checked_mul(b)
safe_quot = a.checked_div(b)
```

### Bitwise Operations

```python
from i24 import I24, U24

a = I24(0b111100001111)
b = I24(0b110011001100)

# Bitwise operators
and_result = a & b    # Bitwise AND
or_result = a | b     # Bitwise OR
xor_result = a ^ b    # Bitwise XOR
not_result = ~a       # Bitwise NOT
left_shift = a << 4   # Left shift
right_shift = a >> 2  # Right shift
```

### Comparison Operations

```python
from i24 import I24

a = I24(1000)
b = I24(2000)

# All standard comparison operators
is_equal = a == b      # Equality
not_equal = a != b     # Inequality
less = a < b           # Less than
less_eq = a <= b       # Less than or equal
greater = a > b        # Greater than
greater_eq = a >= b    # Greater than or equal
```

## Byte Operations and Endianness

All byte operations support three byte orders:

- `'little'`: Little-endian (least significant byte first)
- `'big'`: Big-endian (most significant byte first)
- `'native'`: Native byte order (platform-dependent)

### Converting to Bytes

```python
from i24 import I24

value = I24(0x123456)

# Little-endian (LSB first)
le_bytes = value.to_bytes(byteorder='little')
print(le_bytes)  # b'\x56\x34\x12'

# Big-endian (MSB first)
be_bytes = value.to_bytes(byteorder='big')
print(be_bytes)  # b'\x12\x34\x56'

# Native byte order (platform-dependent)
native_bytes = value.to_bytes(byteorder='native')
```

### Creating from Bytes

```python
from i24 import I24

# From little-endian bytes
bytes_le = bytes([0x12, 0x34, 0x56])
value = I24.from_bytes(bytes_le, byteorder='little')
print(hex(value.to_int()))  # 0x563412

# From big-endian bytes
bytes_be = bytes([0x12, 0x34, 0x56])
value = I24.from_bytes(bytes_be, byteorder='big')
print(hex(value.to_int()))  # 0x123456
```

## Use Cases

### Audio Processing

24-bit integers are commonly used in professional audio applications:

```python
from i24 import I24

# Read 24-bit audio samples
def read_24bit_samples(data: bytes) -> list[I24]:
    samples = []
    for i in range(0, len(data), 3):
        sample_bytes = data[i:i+3]
        sample = I24.from_bytes(sample_bytes, byteorder='little')
        samples.append(sample)
    return samples
```

### Binary Protocols

Handling network protocols with 24-bit fields:

```python
from i24 import U24

# Parse a 24-bit packet ID
packet_bytes = bytes([0x12, 0x34, 0x56])
packet_id = U24.from_bytes(packet_bytes, byteorder='big')
print(f"Packet ID: {packet_id.to_int()}")
```

### Embedded Systems

Working with hardware that uses 24-bit data types:

```python
from i24 import U24

# Read 24-bit sensor value
sensor_data = bytes([0xFF, 0x00, 0x12])
sensor_value = U24.from_bytes(sensor_data, byteorder='little')
print(f"Sensor reading: {sensor_value.to_int()}")
```

## Type Safety

Both `I24` and `U24` are immutable (frozen) types, making them safe for use in multi-threaded environments:

```python
from i24 import I24

value = I24(1000)
# value.some_attribute = 42  # This would raise an error
# I24 instances cannot be modified after creation
```

## Performance

The `i24` package is implemented in Rust using PyO3, providing:

- Near-native performance for arithmetic operations
- Similar to `i32` and `u32` performance


## Documentation

Full documentation is available at: https://jmg049.github.io/i24/

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

Visit the main repository at: https://github.com/jmg049/i24

## License

This project is licensed under MIT - see the [LICENSE](https://github.com/jmg049/i24/blob/main/LICENSE) file for details.

## Links

- **PyPI**: https://pypi.org/project/i24_type/
- **Documentation**: https://jmg049.github.io/i24/
- **Source Code**: https://github.com/jmg049/i24
- **Issue Tracker**: https://github.com/jmg049/i24/issues
- **Changelog**: https://github.com/jmg049/i24/blob/main/CHANGELOG.md

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
