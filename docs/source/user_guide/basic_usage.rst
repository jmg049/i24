Basic Usage
===========

This guide covers the fundamental operations with I24 and U24 types.

Creating Instances
------------------

From Python int
~~~~~~~~~~~~~~~

The most common way to create I24 and U24 values is from Python integers:

.. code-block:: python

   from i24 import I24, U24

   # Create signed 24-bit integer
   signed = I24(1000)
   print(signed)  # I24(1000)

   # Create unsigned 24-bit integer
   unsigned = U24(50000)
   print(unsigned)  # U24(50000)

Value Range Validation
~~~~~~~~~~~~~~~~~~~~~

The constructors automatically validate that values are within the valid range:

.. code-block:: python

   from i24 import I24, U24

   # Valid ranges:
   # I24: -8,388,608 to 8,388,607
   # U24: 0 to 16,777,215

   try:
       # This will raise ValueError (out of range)
       invalid = I24(10_000_000)
   except ValueError as e:
       print(f"Error: {e}")

   try:
       # This will raise ValueError (negative for unsigned)
       invalid = U24(-100)
   except ValueError as e:
       print(f"Error: {e}")

From Bytes
~~~~~~~~~~

Create values from byte sequences with configurable byte order:

.. code-block:: python

   from i24 import I24, U24

   # Little-endian bytes
   bytes_le = bytes([0x00, 0x10, 0x00])
   value = I24.from_bytes(bytes_le, byteorder='little')
   print(value.to_int())  # 4096

   # Big-endian bytes
   bytes_be = bytes([0x00, 0x10, 0x00])
   value = I24.from_bytes(bytes_be, byteorder='big')
   print(value.to_int())  # 4096

   # Native byte order (platform-dependent)
   value = I24.from_bytes(bytes([0x01, 0x02, 0x03]), byteorder='native')

Converting to Python Types
---------------------------

To int
~~~~~~

Convert 24-bit integers to Python int:

.. code-block:: python

   from i24 import I24, U24

   signed = I24(-1000)
   unsigned = U24(2000)

   # Explicit conversion
   int_val = signed.to_int()
   print(int_val)  # -1000

   # Using __int__() magic method
   int_val = int(unsigned)
   print(int_val)  # 2000

To Bytes
~~~~~~~~

Convert to byte sequences:

.. code-block:: python

   from i24 import I24

   value = I24(0x123456)

   # Convert to little-endian bytes
   le_bytes = value.to_bytes(byteorder='little')
   print(le_bytes)  # [86, 52, 18]

   # Convert to big-endian bytes
   be_bytes = value.to_bytes(byteorder='big')
   print(be_bytes)  # [18, 52, 86]

   # Native byte order
   native_bytes = value.to_bytes(byteorder='native')

Comparisons
-----------

I24 and U24 support all standard comparison operators:

.. code-block:: python

   from i24 import I24, U24

   a = I24(100)
   b = I24(200)
   c = I24(100)

   # Equality
   print(a == c)  # True
   print(a == b)  # False
   print(a != b)  # True

   # Ordering
   print(a < b)   # True
   print(a <= c)  # True
   print(b > a)   # True
   print(b >= a)  # True

   # Works with U24 too
   x = U24(1000)
   y = U24(2000)
   print(x < y)   # True

String Representations
----------------------

.. code-block:: python

   from i24 import I24, U24

   value = I24(12345)

   # str() - returns just the number
   print(str(value))   # "12345"

   # repr() - returns the full representation
   print(repr(value))  # "I24(12345)"

   # Works in f-strings
   print(f"Value: {value}")  # "Value: 12345"

Hashing
-------

I24 and U24 are hashable and can be used in sets and as dictionary keys:

.. code-block:: python

   from i24 import I24, U24

   # Use in sets
   values = {I24(100), I24(200), I24(100)}
   print(len(values))  # 2 (duplicates removed)

   # Use as dictionary keys
   mapping = {
       I24(1): "one",
       I24(2): "two",
       U24(100): "hundred"
   }
   print(mapping[I24(1)])  # "one"

Immutability
------------

Both I24 and U24 are **frozen** (immutable) types. Once created, their values cannot be changed:

.. code-block:: python

   from i24 import I24

   value = I24(100)
   
   # This would raise an error if you tried:
   # value.value = 200  # AttributeError: can't set attribute
   
   # Instead, create a new instance
   new_value = I24(200)

Class Attributes
----------------

Access minimum and maximum values:

.. code-block:: python

   from i24 import I24, U24

   # I24 range
   print(I24.min_value)  # I24(-8388608)
   print(I24.max_value)  # I24(8388607)

   # U24 range
   print(U24.min_value)  # U24(0)
   print(U24.max_value)  # U24(16777215)

Type Checking
-------------

.. code-block:: python

   from i24 import I24, U24

   value = I24(100)

   # Check type
   print(isinstance(value, I24))  # True
   print(isinstance(value, U24))  # False

   # Type hints work properly
   def process_signed(val: I24) -> int:
       return val.to_int() * 2

   result = process_signed(value)
   print(result)  # 200
