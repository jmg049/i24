.. i24 documentation master file

i24: 24-bit Integer Types for Python
======================================

.. image:: https://img.shields.io/pypi/v/i24.svg
   :target: https://pypi.org/project/i24/
   :alt: PyPI Version

.. image:: https://img.shields.io/pypi/pyversions/i24.svg
   :target: https://pypi.org/project/i24/
   :alt: Python Versions

The ``i24`` package provides specialized 24-bit integer types for Python: **I24** (signed) and **U24** (unsigned). 
These types are implemented in Rust for high performance and provide a Python interface for working with 
24-bit integers commonly found in audio processing, embedded systems, network protocols, and binary data formats.

Features
--------

* **I24**: 24-bit signed integer (range: -8,388,608 to 8,388,607)
* **U24**: 24-bit unsigned integer (range: 0 to 16,777,215)
* Full arithmetic and bitwise operations with overflow checking
* Conversion to/from Python ``int`` and ``bytes``
* Little-endian, big-endian, and native byte order support
* NumPy integration for array operations
* Immutable (frozen) types for thread safety
* High performance Rust implementation

Quick Start
-----------

Installation
~~~~~~~~~~~~

.. code-block:: bash

   pip install i24

Basic Usage
~~~~~~~~~~~

.. code-block:: python

   from i24 import I24, U24

   # Create 24-bit integers
   signed = I24(1000)
   unsigned = U24(2000)

   # Arithmetic operations
   result = signed + I24(500)
   print(result.to_int())  # 1500

   # Conversion to/from bytes
   bytes_le = [0x00, 0x01, 0x02]
   value = I24.from_bytes(bytes_le, byteorder='little')
   print(value.to_bytes(byteorder='big'))  # [2, 1, 0]

   # Checked arithmetic (returns None on overflow)
   safe_result = I24(8388600).checked_add(I24(100))
   if safe_result is None:
       print("Overflow detected!")

User Guide
----------

.. toctree::
   :maxdepth: 2
   :caption: User Guide

   user_guide/installation
   user_guide/basic_usage
   user_guide/arithmetic
   user_guide/byte_operations

API Reference
-------------

.. toctree::
   :maxdepth: 2
   :caption: API Reference

   api/i24_class
   api/u24_class

Examples
--------

.. toctree::
   :maxdepth: 1
   :caption: Examples

   examples/audio_processing
   examples/binary_protocols
   examples/conversions

Additional Information
----------------------

.. toctree::
   :maxdepth: 1
   :caption: Additional Information

   about/contributing
   about/license

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`

