# Changelog

## \[2.2.0] – 2025-09-02

### Breaking Changes

Breaking things is annoying but I think these changes are important in the long term and better to bite the bullet now.

* The primary types `i24` and `u24` have been moved into their own modules and renamed to `I24` and `U24`.
  This avoids confusion between the crate name (`i24`), the macro (`i24!`), and the struct (`i24`), which previously shared identifiers.
  While the rename requires migration effort, it should reduce long-term ambiguity.
* DiskMethods has been removed in favour of the inherent methods on the `I24` and `U24` types.
  This is a much more focused approach and integrates with the feature-flag system.

### Added

* **`U24` type**: A 24-bit unsigned integer with full arithmetic operations and trait implementations.
* **Bulk I/O methods** on `I24` for safe and unchecked parsing/writing of byte slices:

  * `I24::read_i24s_{be,le,ne}()`
  * `I24::read_i24s_{be,le,ne}_unchecked()` (with `debug_assert!`)
  * `I24::write_i24s_{be,le,ne}()`
* **`u24!` macro** for compile-time checked construction of unsigned 24-bit values.
* **`PackedStruct` trait** for mixed-type serialization.
* **Wire types**: Organises binary format handling (replaces `DiskMethods`).
* **Python bindings**:

  * Full PyO3 integration for `I24` and `U24`.
  * Comprehensive arithmetic, comparison, and bitwise operator support.
* **Safety documentation** for all `unsafe` functions.

### Changed

* **API migration**: `I24DiskMethods` trait is removed in favour of inherent `I24` methods.
* **Improved error handling** in division/remainder operations via correct method resolution.
* **Code organisation**: Large `lib.rs` split into modules (notably a dedicated `types` module).
* **Documentation**: Expanded examples and guidance; warnings enabled for missing docs.
* **Macros**: Extended to support `U24`.

### Technical

* **Clippy warnings**: Targeted lints enabled to maintain code quality.
* **Strict compiler compliance**: Crate now builds cleanly with `-D warnings`.
* **Testing**: Zero regressions; added new property tests.
* **Memory layout verification**: Compile-time assertions for `U24`.
* **Cross-platform correctness**: Proper big-endian and little-endian handling.
* **Inlining**: Reduced from `#[inline(always)]` to `#[inline]`, letting the compiler optimise appropriately.

## [2.1.0] – 2025-04-30

### Added

* **Disk deserialization API** via the new `I24DiskMethods` trait:
  * `read_i24s_{be, le, ne}()` for safe parsing of `&[u8]` into `Vec<i24>`
  * `read_i24s_{be, le, ne}_unchecked()` for fast unchecked variants (assumes length multiple of 3)
  * `write_i24s_{be, le, ne}()` for writing a `&[i24]` as `Vec<u8>` in 3-byte format
* Implemented internal `DiskI24` type to enable zero-copy deserialization using `bytemuck::cast_slice`

### Changed

* Expanded documentation for the `i24` type:
  * Describes memory layout, safety guarantees, `NoUninit` compatibility
  * Details disk I/O patterns and endian-aware methods
* Marked the crate as **safe for use with `bytemuck::NoUninit`** and explained limitations
* Updated README

### Removed

* Removed bytemuck `Pod` trait for `i24` struct.
