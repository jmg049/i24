Arithmetic Operations
=====================

I24 and U24 support comprehensive arithmetic operations with multiple overflow handling strategies.

Basic Arithmetic
----------------

Standard Operators
~~~~~~~~~~~~~~~~~~

The standard arithmetic operators work as expected:

.. code-block:: python

   from i24 import I24, U24

   a = I24(1000)
   b = I24(500)

   # Addition
   result = a + b
   print(result.to_int())  # 1500

   # Subtraction
   result = a - b
   print(result.to_int())  # 500

   # Multiplication
   result = a * b
   print(result.to_int())  # 500000

   # Division
   result = a / b
   print(result)  # 2.0 (returns float)

   # Floor division
   result = a // b
   print(result.to_int())  # 2

   # Modulo
   result = a % b
   print(result.to_int())  # 0

Overflow Behavior
~~~~~~~~~~~~~~~~~

Standard operators raise ``OverflowError`` when results exceed the valid range:

.. code-block:: python

   from i24 import I24

   a = I24(8_000_000)
   b = I24(500_000)

   try:
       # This will overflow
       result = a + b
   except OverflowError as e:
       print(f"Overflow: {e}")

Division by Zero
~~~~~~~~~~~~~~~~

Division operations raise ``ZeroDivisionError``:

.. code-block:: python

   from i24 import I24

   a = I24(1000)
   zero = I24(0)

   try:
       result = a / zero
   except ZeroDivisionError as e:
       print(f"Error: {e}")

Checked Arithmetic
------------------

Checked arithmetic methods return ``None`` on overflow instead of raising exceptions:

Addition
~~~~~~~~

.. code-block:: python

   from i24 import I24

   a = I24(8_000_000)
   b = I24(500_000)

   # Safe addition
   result = a.checked_add(b)
   if result is None:
       print("Addition would overflow")
   else:
       print(f"Result: {result.to_int()}")

   # Successful addition
   c = I24(100)
   d = I24(200)
   result = c.checked_add(d)
   print(result.to_int())  # 300

Subtraction
~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   # Signed subtraction
   a = I24(-8_000_000)
   b = I24(500_000)
   result = a.checked_sub(b)
   if result is None:
       print("Subtraction would underflow")

   # Unsigned subtraction
   x = U24(100)
   y = U24(200)
   result = x.checked_sub(y)
   if result is None:
       print("Cannot subtract larger from smaller for unsigned")

Multiplication
~~~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24

   a = I24(10_000)
   b = I24(1_000)

   result = a.checked_mul(b)
   if result is None:
       print("Multiplication would overflow")
   else:
       print(f"Result: {result.to_int()}")

Division
~~~~~~~~

.. code-block:: python

   from i24 import I24

   a = I24(1000)
   b = I24(0)

   result = a.checked_div(b)
   if result is None:
       print("Division by zero")
   else:
       print(f"Result: {result.to_int()}")

Wrapping Arithmetic
-------------------

Wrapping operations allow overflow/underflow by wrapping around the valid range:

.. code-block:: python

   from i24 import I24, U24

   # I24 wrapping addition
   a = I24(8_388_607)  # I24::MAX
   b = I24(10)
   result = a.wrapping_add(b)
   print(result.to_int())  # Wraps to negative

   # U24 wrapping subtraction
   x = U24(5)
   y = U24(10)
   result = x.wrapping_sub(y)
   print(result.to_int())  # Wraps to large positive

   # Wrapping multiplication
   c = I24(10_000)
   d = I24(2_000)
   result = c.wrapping_mul(d)
   print(result.to_int())  # Wrapped result

Saturating Arithmetic
---------------------

Saturating operations clamp results to the valid range (min/max values):

.. code-block:: python

   from i24 import I24, U24

   # I24 saturating addition
   a = I24(8_388_600)
   b = I24(1_000)
   result = a.saturating_add(b)
   print(result.to_int())  # 8388607 (I24::MAX)

   # I24 saturating subtraction
   c = I24(-8_388_600)
   d = I24(1_000)
   result = c.saturating_sub(d)
   print(result.to_int())  # -8388608 (I24::MIN)

   # U24 saturating operations
   x = U24(16_777_210)
   y = U24(100)
   result = x.saturating_add(y)
   print(result.to_int())  # 16777215 (U24::MAX)

   # Saturating multiplication
   m = I24(100_000)
   n = I24(200)
   result = m.saturating_mul(n)
   print(result.to_int())  # 8388607 (I24::MAX)

Unary Operations
----------------

Negation
~~~~~~~~

.. code-block:: python

   from i24 import I24

   a = I24(1000)
   neg_a = -a
   print(neg_a.to_int())  # -1000

   # Negating I24::MIN raises OverflowError
   min_val = I24.min_value
   try:
       neg_min = -min_val
   except OverflowError as e:
       print(f"Cannot negate MIN: {e}")

Absolute Value
~~~~~~~~~~~~~~

.. code-block:: python

   from i24 import I24

   a = I24(-1000)
   abs_a = abs(a)
   print(abs_a.to_int())  # 1000

   # abs(I24::MIN) raises OverflowError
   min_val = I24.min_value
   try:
       abs_min = abs(min_val)
   except OverflowError as e:
       print(f"Cannot take abs of MIN: {e}")

Positive
~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   a = I24(1000)
   pos_a = +a  # Returns self
   print(pos_a.to_int())  # 1000

Best Practices
--------------

1. **Use checked arithmetic for untrusted input**:

   .. code-block:: python

      def safe_add(a: I24, b: I24) -> I24 | None:
          return a.checked_add(b)

2. **Use saturating arithmetic for clamped values**:

   .. code-block:: python

      # Ensure audio sample never exceeds valid range
      def clamp_sample(value: I24, adjustment: I24) -> I24:
          return value.saturating_add(adjustment)

3. **Use wrapping arithmetic when modular behavior is desired**:

   .. code-block:: python

      # Counter that wraps around
      def increment_counter(counter: U24) -> U24:
          return counter.wrapping_add(U24(1))

4. **Handle exceptions appropriately**:

   .. code-block:: python

      try:
          result = a + b
      except OverflowError:
          # Log error, use fallback, etc.
          result = I24.max_value
