Installation
============

Requirements
------------

* Python 3.10 or later
* NumPy 1.26 or later (automatically installed as a dependency)

Installing from PyPI
--------------------

The recommended way to install ``i24`` is via pip:

.. code-block:: bash

   pip install i24

This will install the latest stable version from PyPI.

Installing a Specific Version
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

To install a specific version:

.. code-block:: bash

   pip install i24==2.2.0

Upgrading
~~~~~~~~~

To upgrade to the latest version:

.. code-block:: bash

   pip install --upgrade i24

Installing from Source
----------------------

For development or to use the latest unreleased features:

.. code-block:: bash

   git clone https://github.com/jmg049/i24.git
   cd i24
   pip install maturin
   maturin develop --release

This requires the Rust toolchain to be installed. Visit https://rustup.rs/ for Rust installation instructions.
