Byte Operations
===============

I24 and U24 provide extensive support for working with binary data and byte representations.

Byte Order (Endianness)
-----------------------

All byte operations support three byte orders:

* ``'little'``: Little-endian (least significant byte first)
* ``'big'``: Big-endian (most significant byte first)
* ``'native'``: Native byte order (platform-dependent)

Converting to Bytes
-------------------

Basic Conversion
~~~~~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   value = I24(0x123456)

   # Little-endian (LSB first)
   le_bytes = value.to_bytes(byteorder='little')
   print(le_bytes)  # [86, 52, 18] (0x56, 0x34, 0x12)

   # Big-endian (MSB first)
   be_bytes = value.to_bytes(byteorder='big')
   print(be_bytes)  # [18, 52, 86] (0x12, 0x34, 0x56)

   # Native byte order (platform-dependent)
   native_bytes = value.to_bytes(byteorder='native')

Signed vs Unsigned
~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   # Negative signed value
   negative = I24(-1000)
   bytes_neg = negative.to_bytes(byteorder='little')
   print(bytes_neg)  # [24, 252, 255] (two's complement)

   # Same bit pattern as unsigned
   unsigned = U24(16776216)  # Equivalent bit pattern
   bytes_pos = unsigned.to_bytes(byteorder='little')
   print(bytes_pos)  # [24, 252, 255]

Creating from Bytes
-------------------

Basic Creation
~~~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   # From little-endian bytes
   bytes_le = bytes([0x12, 0x34, 0x56])
   value = I24.from_bytes(bytes_le, byteorder='little')
   print(hex(value.to_int()))  # 0x563412

   # From big-endian bytes
   bytes_be = bytes([0x12, 0x34, 0x56])
   value = I24.from_bytes(bytes_be, byteorder='big')
   print(hex(value.to_int()))  # 0x123456

   # Default is native byte order
   value = I24.from_bytes(bytes([0x01, 0x02, 0x03]))

Validation
~~~~~~~~~~

The ``from_bytes`` method validates input:

.. code-block:: python

   from i24 import I24

   # Wrong number of bytes
   try:
       value = I24.from_bytes(bytes([0x01, 0x02]), byteorder='little')
   except ValueError as e:
       print(f"Error: {e}")  # bytes must be exactly 3 bytes long

   # Invalid byte order
   try:
       value = I24.from_bytes(bytes([0x01, 0x02, 0x03]), byteorder='middle')
   except ValueError as e:
       print(f"Error: {e}")  # byteorder must be 'little', 'big', or 'native'


Bitwise Operations
------------------

I24 and U24 support all standard bitwise operations:

AND, OR, XOR
~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   a = I24(0b111100001111)
   b = I24(0b110011001100)

   # Bitwise AND
   result = a & b
   print(bin(result.to_int()))  # 0b110000001100

   # Bitwise OR
   result = a | b
   print(bin(result.to_int()))  # 0b111111001111

   # Bitwise XOR
   result = a ^ b
   print(bin(result.to_int()))  # 0b001111000011

Bitwise NOT
~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   value = I24(0b111100001111)
   inverted = ~value
   print(bin(inverted.to_int() & 0xFFFFFF))  # Inverted bits

Left and Right Shift
~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   value = I24(0b1111)

   # Left shift
   shifted = value << 4
   print(bin(shifted.to_int()))  # 0b11110000

   # Right shift
   shifted = value >> 2
   print(bin(shifted.to_int()))  # 0b11

   # Shift with overflow detection
   large = I24(0x100000)
   try:
       result = large << 8  # Would exceed 24 bits
   except OverflowError as e:
       print(f"Shift overflow: {e}")

Bit Manipulation Methods
------------------------

Counting Bits
~~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   value = U24(0b11110000111100001111)

   # Count one bits
   ones = value.count_ones()
   print(ones)  # 12

   # Count zero bits
   zeros = value.count_zeros()
   print(zeros)  # 20

   # Leading zeros
   leading = value.leading_zeros()
   print(leading)  # Number of leading zero bits

   # Trailing zeros
   trailing = value.trailing_zeros()
   print(trailing)  # Number of trailing zero bits

Bit Length
~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   value = U24(255)  # 0b11111111

   # Number of bits needed to represent the value
   bits_needed = value.bit_length()
   print(bits_needed)  # 8

   # Bit count (number of 1 bits)
   bit_count = value.bit_count()
   print(bit_count)  # 8
