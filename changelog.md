# Changelog

## [2.1.0] – 2025-04-30

### Added

- **Disk deserialization API** via the new `I24DiskMethods` trait:
  - `read_i24s_{be, le, ne}()` for safe parsing of `&[u8]` into `Vec<i24>`
  - `read_i24s_{be, le, ne}_unchecked()` for fast unchecked variants (assumes length multiple of 3)
  - `write_i24s_{be, le, ne}()` for writing a `&[i24]` as `Vec<u8>` in 3-byte format
- Implemented internal `DiskI24` type to enable zero-copy deserialization using `bytemuck::cast_slice`

### Changed

- Expanded documentation for the `i24` type:
  - Describes memory layout, safety guarantees, `NoUninit` compatibility
  - Details disk I/O patterns and endian-aware methods
- Marked the crate as **safe for use with `bytemuck::NoUninit`** and explained limitations
- Updated README

### Removed

- Removed bytemuck `Pod` trait for `i24` struct.
