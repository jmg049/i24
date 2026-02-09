"""
Python stub file for the i24 module.

This module provides 24-bit signed (I24) and unsigned (U24) integer types
implemented in Rust and exposed to Python via PyO3.
"""

from typing import Literal, Optional, final

__version__: str

@final
class I24:
    """
    A 24-bit signed integer type.

    Valid range: -8,388,608 to 8,388,607 (-2^23 to 2^23 - 1)

    This class provides a frozen (immutable) wrapper around a Rust I24 type,
    with support for arithmetic operations, bitwise operations, and conversions
    to/from Python int and bytes.
    """

    min_value: I24
    """The minimum value for I24: -8,388,608"""

    max_value: I24
    """The maximum value for I24: 8,388,607"""

    def __init__(self, value: int) -> None:
        """
        Create a new I24 from a Python int.

        Args:
            value: An integer in the range [-8388608, 8388607]

        Raises:
            ValueError: If value is out of range for I24
        """
        ...

    @staticmethod
    def from_bytes(
        bytes: bytes, byteorder: Literal["little", "big", "native"] = "native"
    ) -> I24:
        """
        Create an I24 from a list of 3 bytes.

        Args:
            bytes: 3 bytes representing some integer (0-255)
            byteorder: Byte order for interpretation ('little', 'big', or 'native')

        Returns:
            A new I24 instance

        Raises:
            ValueError: If bytes list is not exactly 3 bytes long or byteorder is invalid
        """
        ...

    def to_int(self) -> int:
        """
        Convert this I24 to a Python int.

        Returns:
            The I24 value as a Python int
        """
        ...

    def to_bytes(
        self, byteorder: Literal["little", "big", "native"] = "native"
    ) -> bytes:
        """
        Convert this I24 to a bytes object.

        Args:
            byteorder: Byte order for conversion ('little', 'big', or 'native')

        Returns:
            A bytes object of length 3 representing the I24 value

        Raises:
            ValueError: If byteorder is invalid
        """
        ...

    # Comparison operators
    def __eq__(self, other: object) -> bool: ...
    def __ne__(self, other: object) -> bool: ...
    def __lt__(self, other: I24) -> bool: ...
    def __le__(self, other: I24) -> bool: ...
    def __gt__(self, other: I24) -> bool: ...
    def __ge__(self, other: I24) -> bool: ...

    # Arithmetic operators
    def __add__(self, other: I24) -> I24:
        """
        Add two I24 values.

        Raises:
            OverflowError: If the result overflows I24 range
        """
        ...

    def __sub__(self, other: I24) -> I24:
        """
        Subtract two I24 values.

        Raises:
            OverflowError: If the result overflows I24 range
        """
        ...

    def __mul__(self, other: I24) -> I24:
        """
        Multiply two I24 values.

        Raises:
            OverflowError: If the result overflows I24 range
        """
        ...

    def __truediv__(self, other: I24) -> float:
        """
        Divide two I24 values (true division, returns float).

        Raises:
            ZeroDivisionError: If dividing by zero
        """
        ...

    def __floordiv__(self, other: I24) -> I24:
        """
        Floor divide two I24 values.

        Raises:
            ZeroDivisionError: If dividing by zero
        """
        ...

    def __mod__(self, other: I24) -> I24:
        """
        Modulo operation on two I24 values.

        Raises:
            ZeroDivisionError: If dividing by zero
        """
        ...

    # Bitwise operations
    def __and__(self, other: I24) -> I24:
        """Bitwise AND operation."""
        ...

    def __or__(self, other: I24) -> I24:
        """Bitwise OR operation."""
        ...

    def __xor__(self, other: I24) -> I24:
        """Bitwise XOR operation."""
        ...

    def __lshift__(self, other: int) -> I24:
        """
        Left shift operation.

        Raises:
            ValueError: If shift count is out of range (>= 32)
            OverflowError: If the result overflows I24 range
        """
        ...

    def __rshift__(self, other: int) -> I24:
        """
        Right shift operation.

        Raises:
            ValueError: If shift count is out of range (>= 32)
        """
        ...

    def __invert__(self) -> I24:
        """Bitwise NOT operation."""
        ...

    # Unary operators
    def __neg__(self) -> I24:
        """
        Negate this I24 value.

        Raises:
            OverflowError: If negating I24::MIN
        """
        ...

    def __pos__(self) -> I24:
        """Unary positive (returns self)."""
        ...

    def __abs__(self) -> I24:
        """
        Absolute value.

        Raises:
            OverflowError: If called on I24::MIN
        """
        ...

    # Conversion methods
    def __int__(self) -> int:
        """Convert to Python int."""
        ...

    def __str__(self) -> str:
        """String representation (the numeric value)."""
        ...

    def __repr__(self) -> str:
        """Developer-friendly representation."""
        ...

    def __hash__(self) -> int:
        """Hash value for use in sets and dicts."""
        ...

    # Rounding methods
    def __round__(self, ndigits: Optional[int] = None) -> I24:
        """Round to nearest integer (returns self for I24)."""
        ...

    def __ceil__(self) -> I24:
        """Ceiling (returns self for I24)."""
        ...

    def __floor__(self) -> I24:
        """Floor (returns self for I24)."""
        ...

    def __trunc__(self) -> I24:
        """Truncate (returns self for I24)."""
        ...

    # Bit manipulation methods
    def count_ones(self) -> int:
        """Count the number of one bits in the binary representation."""
        ...

    def count_zeros(self) -> int:
        """Count the number of zero bits in the binary representation."""
        ...

    def leading_zeros(self) -> int:
        """Count the number of leading zero bits."""
        ...

    def trailing_zeros(self) -> int:
        """Count the number of trailing zero bits."""
        ...

    def bit_length(self) -> int:
        """Number of bits necessary to represent this value."""
        ...

    def bit_count(self) -> int:
        """Number of one bits in the absolute value."""
        ...

    # Checked arithmetic methods
    def checked_add(self, other: I24) -> Optional[I24]:
        """
        Checked addition. Returns None on overflow.

        Args:
            other: The I24 value to add

        Returns:
            The result if it fits in I24, None otherwise
        """
        ...

    def checked_sub(self, other: I24) -> Optional[I24]:
        """
        Checked subtraction. Returns None on overflow.

        Args:
            other: The I24 value to subtract

        Returns:
            The result if it fits in I24, None otherwise
        """
        ...

    def checked_mul(self, other: I24) -> Optional[I24]:
        """
        Checked multiplication. Returns None on overflow.

        Args:
            other: The I24 value to multiply

        Returns:
            The result if it fits in I24, None otherwise
        """
        ...

    def checked_div(self, other: I24) -> Optional[I24]:
        """
        Checked division. Returns None on division by zero.

        Args:
            other: The I24 value to divide by

        Returns:
            The result, or None if dividing by zero
        """
        ...

    # Wrapping arithmetic methods
    def wrapping_add(self, other: I24) -> I24:
        """
        Wrapping addition. Wraps on overflow.

        Args:
            other: The I24 value to add

        Returns:
            The wrapped result
        """
        ...

    def wrapping_sub(self, other: I24) -> I24:
        """
        Wrapping subtraction. Wraps on overflow.

        Args:
            other: The I24 value to subtract

        Returns:
            The wrapped result
        """
        ...

    def wrapping_mul(self, other: I24) -> I24:
        """
        Wrapping multiplication. Wraps on overflow.

        Args:
            other: The I24 value to multiply

        Returns:
            The wrapped result
        """
        ...

    # Saturating arithmetic methods
    def saturating_add(self, other: I24) -> I24:
        """
        Saturating addition. Clamps to min/max on overflow.

        Args:
            other: The I24 value to add

        Returns:
            The result, clamped to I24 range
        """
        ...

    def saturating_sub(self, other: I24) -> I24:
        """
        Saturating subtraction. Clamps to min/max on overflow.

        Args:
            other: The I24 value to subtract

        Returns:
            The result, clamped to I24 range
        """
        ...

    def saturating_mul(self, other: I24) -> I24:
        """
        Saturating multiplication. Clamps to min/max on overflow.

        Args:
            other: The I24 value to multiply

        Returns:
            The result, clamped to I24 range
        """
        ...

    def as_integer_ratio(self) -> tuple[int, int]:
        """
        Return integer ratio (self, 1).

        Returns:
            A tuple of (numerator, denominator) = (self.to_int(), 1)
        """
        ...

@final
class U24:
    """
    A 24-bit unsigned integer type.

    Valid range: 0 to 16,777,215 (0 to 2^24 - 1)

    This class provides a frozen (immutable) wrapper around a Rust U24 type,
    with support for arithmetic operations, bitwise operations, and conversions
    to/from Python int and bytes.
    """

    min_value: U24
    """The minimum value for U24: 0"""

    max_value: U24
    """The maximum value for U24: 16,777,215"""

    def __init__(self, value: int) -> None:
        """
        Create a new U24 from a Python int.

        Args:
            value: An integer in the range [0, 16777215]

        Raises:
            ValueError: If value is out of range for U24
        """
        ...

    @staticmethod
    def from_bytes(
        bytes: list[int], byteorder: Literal["little", "big", "native"] = "native"
    ) -> U24:
        """
        Create a U24 from a list of 3 bytes.

        Args:
            bytes: A list of exactly 3 integers (0-255) representing bytes
            byteorder: Byte order for interpretation ('little', 'big', or 'native')

        Returns:
            A new U24 instance

        Raises:
            ValueError: If bytes list is not exactly 3 bytes long or byteorder is invalid
        """
        ...

    def to_int(self) -> int:
        """
        Convert this U24 to a Python int.

        Returns:
            The U24 value as a Python int
        """
        ...

    def to_bytes(
        self, byteorder: Literal["little", "big", "native"] = "native"
    ) -> list[int]:
        """
        Convert this U24 to a list of bytes.

        Args:
            byteorder: Byte order for conversion ('little', 'big', or 'native')

        Returns:
            A list of 3 integers (0-255) representing the bytes

        Raises:
            ValueError: If byteorder is invalid
        """
        ...

    # Comparison operators
    def __eq__(self, other: object) -> bool: ...
    def __ne__(self, other: object) -> bool: ...
    def __lt__(self, other: U24) -> bool: ...
    def __le__(self, other: U24) -> bool: ...
    def __gt__(self, other: U24) -> bool: ...
    def __ge__(self, other: U24) -> bool: ...

    # Arithmetic operators
    def __add__(self, other: U24) -> U24:
        """
        Add two U24 values.

        Raises:
            OverflowError: If the result overflows U24 range
        """
        ...

    def __sub__(self, other: U24) -> U24:
        """
        Subtract two U24 values.

        Raises:
            OverflowError: If the result overflows U24 range
        """
        ...

    def __mul__(self, other: U24) -> U24:
        """
        Multiply two U24 values.

        Raises:
            OverflowError: If the result overflows U24 range
        """
        ...

    def __truediv__(self, other: U24) -> float:
        """
        Divide two U24 values (true division, returns float).

        Raises:
            ZeroDivisionError: If dividing by zero
        """
        ...

    def __floordiv__(self, other: U24) -> U24:
        """
        Floor divide two U24 values.

        Raises:
            ZeroDivisionError: If dividing by zero
        """
        ...

    def __mod__(self, other: U24) -> U24:
        """
        Modulo operation on two U24 values.

        Raises:
            ZeroDivisionError: If dividing by zero
        """
        ...

    # Bitwise operations
    def __and__(self, other: U24) -> U24:
        """Bitwise AND operation."""
        ...

    def __or__(self, other: U24) -> U24:
        """Bitwise OR operation."""
        ...

    def __xor__(self, other: U24) -> U24:
        """Bitwise XOR operation."""
        ...

    def __lshift__(self, other: int) -> U24:
        """
        Left shift operation.

        Raises:
            ValueError: If shift count is out of range (>= 32)
            OverflowError: If the result overflows U24 range
        """
        ...

    def __rshift__(self, other: int) -> U24:
        """
        Right shift operation.

        Raises:
            ValueError: If shift count is out of range (>= 32)
        """
        ...

    def __invert__(self) -> U24:
        """Bitwise NOT operation."""
        ...

    # Unary operators
    def __pos__(self) -> U24:
        """Unary positive (returns self)."""
        ...

    # Conversion methods
    def __int__(self) -> int:
        """Convert to Python int."""
        ...

    def __str__(self) -> str:
        """String representation (the numeric value)."""
        ...

    def __repr__(self) -> str:
        """Developer-friendly representation."""
        ...

    def __hash__(self) -> int:
        """Hash value for use in sets and dicts."""
        ...

    # Rounding methods
    def __round__(self, ndigits: Optional[int] = None) -> U24:
        """Round to nearest integer (returns self for U24)."""
        ...

    def __ceil__(self) -> U24:
        """Ceiling (returns self for U24)."""
        ...

    def __floor__(self) -> U24:
        """Floor (returns self for U24)."""
        ...

    def __trunc__(self) -> U24:
        """Truncate (returns self for U24)."""
        ...

    # Bit manipulation methods
    def count_ones(self) -> int:
        """Count the number of one bits in the binary representation."""
        ...

    def count_zeros(self) -> int:
        """Count the number of zero bits in the binary representation."""
        ...

    def leading_zeros(self) -> int:
        """Count the number of leading zero bits."""
        ...

    def trailing_zeros(self) -> int:
        """Count the number of trailing zero bits."""
        ...

    def bit_length(self) -> int:
        """Number of bits necessary to represent this value."""
        ...

    def bit_count(self) -> int:
        """Number of one bits in the value."""
        ...

    # Checked arithmetic methods
    def checked_add(self, other: U24) -> Optional[U24]:
        """
        Checked addition. Returns None on overflow.

        Args:
            other: The U24 value to add

        Returns:
            The result if it fits in U24, None otherwise
        """
        ...

    def checked_sub(self, other: U24) -> Optional[U24]:
        """
        Checked subtraction. Returns None on overflow.

        Args:
            other: The U24 value to subtract

        Returns:
            The result if it fits in U24, None otherwise
        """
        ...

    def checked_mul(self, other: U24) -> Optional[U24]:
        """
        Checked multiplication. Returns None on overflow.

        Args:
            other: The U24 value to multiply

        Returns:
            The result if it fits in U24, None otherwise
        """
        ...

    def checked_div(self, other: U24) -> Optional[U24]:
        """
        Checked division. Returns None on division by zero.

        Args:
            other: The U24 value to divide by

        Returns:
            The result, or None if dividing by zero
        """
        ...

    # Wrapping arithmetic methods
    def wrapping_add(self, other: U24) -> U24:
        """
        Wrapping addition. Wraps on overflow.

        Args:
            other: The U24 value to add

        Returns:
            The wrapped result
        """
        ...

    def wrapping_sub(self, other: U24) -> U24:
        """
        Wrapping subtraction. Wraps on overflow.

        Args:
            other: The U24 value to subtract

        Returns:
            The wrapped result
        """
        ...

    def wrapping_mul(self, other: U24) -> U24:
        """
        Wrapping multiplication. Wraps on overflow.

        Args:
            other: The U24 value to multiply

        Returns:
            The wrapped result
        """
        ...

    # Saturating arithmetic methods
    def saturating_add(self, other: U24) -> U24:
        """
        Saturating addition. Clamps to min/max on overflow.

        Args:
            other: The U24 value to add

        Returns:
            The result, clamped to U24 range
        """
        ...

    def saturating_sub(self, other: U24) -> U24:
        """
        Saturating subtraction. Clamps to min/max on overflow.

        Args:
            other: The U24 value to subtract

        Returns:
            The result, clamped to U24 range
        """
        ...

    def saturating_mul(self, other: U24) -> U24:
        """
        Saturating multiplication. Clamps to min/max on overflow.

        Args:
            other: The U24 value to multiply

        Returns:
            The result, clamped to U24 range
        """
        ...

    def as_integer_ratio(self) -> tuple[int, int]:
        """
        Return integer ratio (self, 1).

        Returns:
            A tuple of (numerator, denominator) = (self.to_int(), 1)
        """
        ...
