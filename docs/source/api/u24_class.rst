U24 Class
=========

.. class:: U24(value: int)

   A 24-bit unsigned integer type with range 0 to 16,777,215.

   The U24 class is implemented in Rust and provides a frozen (immutable) Python wrapper
   for 24-bit unsigned integer operations. It supports all standard arithmetic, comparison,
   and bitwise operations with appropriate overflow checking.

   :param value: An integer in the range [0, 16,777,215]
   :type value: int
   :raises ValueError: If value is out of range for U24

   **Example**::

      from i24 import U24

      x = U24(1000)
      y = U24(500)
      result = x + y
      print(result.to_int())  # 1500

Class Attributes
----------------

.. attribute:: U24.min_value
   :type: U24

   The minimum value for U24: ``U24(0)``

.. attribute:: U24.max_value
   :type: U24

   The maximum value for U24: ``U24(16777215)``

Construction Methods
--------------------

.. method:: U24.__init__(value: int) -> None

   Create a new U24 from a Python int.

   :param value: An integer in the range [0, 16,777,215]
   :raises ValueError: If value is out of range

.. staticmethod:: U24.from_bytes(bytes: list[int], byteorder: Literal['little', 'big', 'native'] = 'native') -> U24

   Create a U24 from a list of 3 bytes.

   :param bytes: A list of exactly 3 integers (0-255) representing bytes
   :param byteorder: Byte order for interpretation ('little', 'big', or 'native')
   :return: A new U24 instance
   :raises ValueError: If bytes list is not exactly 3 bytes long or byteorder is invalid

   **Example**::

      bytes_le = [0xFF, 0xFF, 0xFF]
      value = U24.from_bytes(bytes_le, byteorder='little')  # 16777215

Conversion Methods
------------------

.. method:: U24.to_int() -> int

   Convert this U24 to a Python int.

   :return: The U24 value as a Python int

   **Example**::

      x = U24(1000)
      print(x.to_int())  # 1000

.. method:: U24.to_bytes(byteorder: Literal['little', 'big', 'native'] = 'native') -> list[int]

   Convert this U24 to a list of bytes.

   :param byteorder: Byte order for conversion ('little', 'big', or 'native')
   :return: A list of 3 integers (0-255) representing the bytes
   :raises ValueError: If byteorder is invalid

   **Example**::

      value = U24(0x123456)
      be_bytes = value.to_bytes(byteorder='big')  # [18, 52, 86]

Comparison Operators
--------------------

.. method:: U24.__eq__(other: object) -> bool

   Test for equality.

.. method:: U24.__ne__(other: object) -> bool

   Test for inequality.

.. method:: U24.__lt__(other: U24) -> bool

   Test if less than.

.. method:: U24.__le__(other: U24) -> bool

   Test if less than or equal.

.. method:: U24.__gt__(other: U24) -> bool

   Test if greater than.

.. method:: U24.__ge__(other: U24) -> bool

   Test if greater than or equal.

Arithmetic Operators
--------------------

.. method:: U24.__add__(other: U24) -> U24

   Add two U24 values.

   :raises OverflowError: If the result overflows U24 range

.. method:: U24.__sub__(other: U24) -> U24

   Subtract two U24 values.

   :raises OverflowError: If the result overflows U24 range

.. method:: U24.__mul__(other: U24) -> U24

   Multiply two U24 values.

   :raises OverflowError: If the result overflows U24 range

.. method:: U24.__truediv__(other: U24) -> float

   Divide two U24 values (true division, returns float).

   :raises ZeroDivisionError: If dividing by zero

.. method:: U24.__floordiv__(other: U24) -> U24

   Floor divide two U24 values.

   :raises ZeroDivisionError: If dividing by zero

.. method:: U24.__mod__(other: U24) -> U24

   Modulo operation on two U24 values.

   :raises ZeroDivisionError: If dividing by zero

Bitwise Operators
-----------------

.. method:: U24.__and__(other: U24) -> U24

   Bitwise AND operation.

.. method:: U24.__or__(other: U24) -> U24

   Bitwise OR operation.

.. method:: U24.__xor__(other: U24) -> U24

   Bitwise XOR operation.

.. method:: U24.__lshift__(other: int) -> U24

   Left shift operation.

   :raises ValueError: If shift count is out of range (>= 32)
   :raises OverflowError: If the result overflows U24 range

.. method:: U24.__rshift__(other: int) -> U24

   Right shift operation.

   :raises ValueError: If shift count is out of range (>= 32)

.. method:: U24.__invert__() -> U24

   Bitwise NOT operation.

Unary Operators
---------------

.. method:: U24.__pos__() -> U24

   Unary positive (returns self).

Special Methods
---------------

.. method:: U24.__int__() -> int

   Convert to Python int.

.. method:: U24.__str__() -> str

   String representation (the numeric value).

.. method:: U24.__repr__() -> str

   Developer-friendly representation.

.. method:: U24.__hash__() -> int

   Hash value for use in sets and dicts.

Rounding Methods
----------------

.. method:: U24.__round__(ndigits: Optional[int] = None) -> U24

   Round to nearest integer (returns self for U24).

.. method:: U24.__ceil__() -> U24

   Ceiling (returns self for U24).

.. method:: U24.__floor__() -> U24

   Floor (returns self for U24).

.. method:: U24.__trunc__() -> U24

   Truncate (returns self for U24).

Bit Manipulation Methods
------------------------

.. method:: U24.count_ones() -> int

   Count the number of one bits in the binary representation.

.. method:: U24.count_zeros() -> int

   Count the number of zero bits in the binary representation.

.. method:: U24.leading_zeros() -> int

   Count the number of leading zero bits.

.. method:: U24.trailing_zeros() -> int

   Count the number of trailing zero bits.

.. method:: U24.bit_length() -> int

   Number of bits necessary to represent this value.

.. method:: U24.bit_count() -> int

   Number of one bits in the value.

Checked Arithmetic Methods
--------------------------

.. method:: U24.checked_add(other: U24) -> Optional[U24]

   Checked addition. Returns None on overflow.

   :param other: The U24 value to add
   :return: The result if it fits in U24, None otherwise

.. method:: U24.checked_sub(other: U24) -> Optional[U24]

   Checked subtraction. Returns None on overflow.

   :param other: The U24 value to subtract
   :return: The result if it fits in U24, None otherwise

.. method:: U24.checked_mul(other: U24) -> Optional[U24]

   Checked multiplication. Returns None on overflow.

   :param other: The U24 value to multiply
   :return: The result if it fits in U24, None otherwise

.. method:: U24.checked_div(other: U24) -> Optional[U24]

   Checked division. Returns None on division by zero.

   :param other: The U24 value to divide by
   :return: The result, or None if dividing by zero

Wrapping Arithmetic Methods
---------------------------

.. method:: U24.wrapping_add(other: U24) -> U24

   Wrapping addition. Wraps on overflow.

   :param other: The U24 value to add
   :return: The wrapped result

.. method:: U24.wrapping_sub(other: U24) -> U24

   Wrapping subtraction. Wraps on overflow.

   :param other: The U24 value to subtract
   :return: The wrapped result

.. method:: U24.wrapping_mul(other: U24) -> U24

   Wrapping multiplication. Wraps on overflow.

   :param other: The U24 value to multiply
   :return: The wrapped result

Saturating Arithmetic Methods
------------------------------

.. method:: U24.saturating_add(other: U24) -> U24

   Saturating addition. Clamps to min/max on overflow.

   :param other: The U24 value to add
   :return: The result, clamped to U24 range

.. method:: U24.saturating_sub(other: U24) -> U24

   Saturating subtraction. Clamps to min/max on overflow.

   :param other: The U24 value to subtract
   :return: The result, clamped to U24 range

.. method:: U24.saturating_mul(other: U24) -> U24

   Saturating multiplication. Clamps to min/max on overflow.

   :param other: The U24 value to multiply
   :return: The result, clamped to U24 range

Utility Methods
---------------

.. method:: U24.as_integer_ratio() -> Tuple[int, int]

   Return integer ratio (self, 1).

   :return: A tuple of (numerator, denominator) = (self.to_int(), 1)
