I24 Class
=========

.. class:: I24(value: int)

   A 24-bit signed integer type with range -8,388,608 to 8,388,607.

   The I24 class is implemented in Rust and provides a frozen (immutable) Python wrapper
   for 24-bit signed integer operations. It supports all standard arithmetic, comparison,
   and bitwise operations with appropriate overflow checking.

   :param value: An integer in the range [-8,388,608, 8,388,607]
   :type value: int
   :raises ValueError: If value is out of range for I24

   **Example**::

      from i24 import I24

      x = I24(1000)
      y = I24(-500)
      result = x + y
      print(result.to_int())  # 500

Class Attributes
----------------

.. attribute:: I24.min_value
   :type: I24

   The minimum value for I24: ``I24(-8388608)``

.. attribute:: I24.max_value
   :type: I24

   The maximum value for I24: ``I24(8388607)``

Construction Methods
--------------------

.. method:: I24.__init__(value: int) -> None

   Create a new I24 from a Python int.

   :param value: An integer in the range [-8,388,608, 8,388,607]
   :raises ValueError: If value is out of range

.. staticmethod:: I24.from_bytes(bytes: list[int], byteorder: Literal['little', 'big', 'native'] = 'native') -> I24

   Create an I24 from a list of 3 bytes.

   :param bytes: A list of exactly 3 integers (0-255) representing bytes
   :param byteorder: Byte order for interpretation ('little', 'big', or 'native')
   :return: A new I24 instance
   :raises ValueError: If bytes list is not exactly 3 bytes long or byteorder is invalid

   **Example**::

      bytes_le = [0x00, 0x10, 0x00]
      value = I24.from_bytes(bytes_le, byteorder='little')

Conversion Methods
------------------

.. method:: I24.to_int() -> int

   Convert this I24 to a Python int.

   :return: The I24 value as a Python int

   **Example**::

      x = I24(1000)
      print(x.to_int())  # 1000

.. method:: I24.to_bytes(byteorder: Literal['little', 'big', 'native'] = 'native') -> list[int]

   Convert this I24 to a list of bytes.

   :param byteorder: Byte order for conversion ('little', 'big', or 'native')
   :return: A list of 3 integers (0-255) representing the bytes
   :raises ValueError: If byteorder is invalid

   **Example**::

      value = I24(0x123456)
      be_bytes = value.to_bytes(byteorder='big')  # [18, 52, 86]

Comparison Operators
--------------------

.. method:: I24.__eq__(other: object) -> bool

   Test for equality.

.. method:: I24.__ne__(other: object) -> bool

   Test for inequality.

.. method:: I24.__lt__(other: I24) -> bool

   Test if less than.

.. method:: I24.__le__(other: I24) -> bool

   Test if less than or equal.

.. method:: I24.__gt__(other: I24) -> bool

   Test if greater than.

.. method:: I24.__ge__(other: I24) -> bool

   Test if greater than or equal.

Arithmetic Operators
--------------------

.. method:: I24.__add__(other: I24) -> I24

   Add two I24 values.

   :raises OverflowError: If the result overflows I24 range

.. method:: I24.__sub__(other: I24) -> I24

   Subtract two I24 values.

   :raises OverflowError: If the result overflows I24 range

.. method:: I24.__mul__(other: I24) -> I24

   Multiply two I24 values.

   :raises OverflowError: If the result overflows I24 range

.. method:: I24.__truediv__(other: I24) -> float

   Divide two I24 values (true division, returns float).

   :raises ZeroDivisionError: If dividing by zero

.. method:: I24.__floordiv__(other: I24) -> I24

   Floor divide two I24 values.

   :raises ZeroDivisionError: If dividing by zero

.. method:: I24.__mod__(other: I24) -> I24

   Modulo operation on two I24 values.

   :raises ZeroDivisionError: If dividing by zero

Bitwise Operators
-----------------

.. method:: I24.__and__(other: I24) -> I24

   Bitwise AND operation.

.. method:: I24.__or__(other: I24) -> I24

   Bitwise OR operation.

.. method:: I24.__xor__(other: I24) -> I24

   Bitwise XOR operation.

.. method:: I24.__lshift__(other: int) -> I24

   Left shift operation.

   :raises ValueError: If shift count is out of range (>= 32)
   :raises OverflowError: If the result overflows I24 range

.. method:: I24.__rshift__(other: int) -> I24

   Right shift operation.

   :raises ValueError: If shift count is out of range (>= 32)

.. method:: I24.__invert__() -> I24

   Bitwise NOT operation.

Unary Operators
---------------

.. method:: I24.__neg__() -> I24

   Negate this I24 value.

   :raises OverflowError: If negating I24::MIN

.. method:: I24.__pos__() -> I24

   Unary positive (returns self).

.. method:: I24.__abs__() -> I24

   Absolute value.

   :raises OverflowError: If called on I24::MIN

Special Methods
---------------

.. method:: I24.__int__() -> int

   Convert to Python int.

.. method:: I24.__str__() -> str

   String representation (the numeric value).

.. method:: I24.__repr__() -> str

   Developer-friendly representation.

.. method:: I24.__hash__() -> int

   Hash value for use in sets and dicts.

Rounding Methods
----------------

.. method:: I24.__round__(ndigits: Optional[int] = None) -> I24

   Round to nearest integer (returns self for I24).

.. method:: I24.__ceil__() -> I24

   Ceiling (returns self for I24).

.. method:: I24.__floor__() -> I24

   Floor (returns self for I24).

.. method:: I24.__trunc__() -> I24

   Truncate (returns self for I24).

Bit Manipulation Methods
------------------------

.. method:: I24.count_ones() -> int

   Count the number of one bits in the binary representation.

.. method:: I24.count_zeros() -> int

   Count the number of zero bits in the binary representation.

.. method:: I24.leading_zeros() -> int

   Count the number of leading zero bits.

.. method:: I24.trailing_zeros() -> int

   Count the number of trailing zero bits.

.. method:: I24.bit_length() -> int

   Number of bits necessary to represent this value.

.. method:: I24.bit_count() -> int

   Number of one bits in the absolute value.

Checked Arithmetic Methods
--------------------------

.. method:: I24.checked_add(other: I24) -> Optional[I24]

   Checked addition. Returns None on overflow.

   :param other: The I24 value to add
   :return: The result if it fits in I24, None otherwise

.. method:: I24.checked_sub(other: I24) -> Optional[I24]

   Checked subtraction. Returns None on overflow.

   :param other: The I24 value to subtract
   :return: The result if it fits in I24, None otherwise

.. method:: I24.checked_mul(other: I24) -> Optional[I24]

   Checked multiplication. Returns None on overflow.

   :param other: The I24 value to multiply
   :return: The result if it fits in I24, None otherwise

.. method:: I24.checked_div(other: I24) -> Optional[I24]

   Checked division. Returns None on division by zero.

   :param other: The I24 value to divide by
   :return: The result, or None if dividing by zero

Wrapping Arithmetic Methods
---------------------------

.. method:: I24.wrapping_add(other: I24) -> I24

   Wrapping addition. Wraps on overflow.

   :param other: The I24 value to add
   :return: The wrapped result

.. method:: I24.wrapping_sub(other: I24) -> I24

   Wrapping subtraction. Wraps on overflow.

   :param other: The I24 value to subtract
   :return: The wrapped result

.. method:: I24.wrapping_mul(other: I24) -> I24

   Wrapping multiplication. Wraps on overflow.

   :param other: The I24 value to multiply
   :return: The wrapped result

Saturating Arithmetic Methods
------------------------------

.. method:: I24.saturating_add(other: I24) -> I24

   Saturating addition. Clamps to min/max on overflow.

   :param other: The I24 value to add
   :return: The result, clamped to I24 range

.. method:: I24.saturating_sub(other: I24) -> I24

   Saturating subtraction. Clamps to min/max on overflow.

   :param other: The I24 value to subtract
   :return: The result, clamped to I24 range

.. method:: I24.saturating_mul(other: I24) -> I24

   Saturating multiplication. Clamps to min/max on overflow.

   :param other: The I24 value to multiply
   :return: The result, clamped to I24 range

Utility Methods
---------------

.. method:: I24.as_integer_ratio() -> Tuple[int, int]

   Return integer ratio (self, 1).

   :return: A tuple of (numerator, denominator) = (self.to_int(), 1)
