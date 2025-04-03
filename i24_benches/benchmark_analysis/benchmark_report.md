# i24 Benchmark Results

*Generated on: 2025-04-29T12:16:37.682921433+01:00*

## System Information

- **CPU:** 24 cores
- **Memory:** 64136 MB
- **OS:** Linux 6.11.0-24-generic
- **Rust Version:** 1.85.0

## Executive Summary

![Durations overview per operation](./operation_durations.png)

- i24 performs better than i32 in **7** operations and worse in **5** operations.
- Best relative performance: **LeftShift** (1.12x of i32 performance)
- Worst relative performance: **Remainder** (0.35x of i32 performance)

## Performance by Category

| Category   | Average Performance   |
|:-----------|:----------------------|
| Shift      | 1.01x                 |
| Bitwise    | 1.01x                 |
| Unary      | 0.88x                 |
| Arithmetic | 0.81x                 |

## Detailed Benchmark Results

### Throughput (Operations per second)

| operation      | i24                     | i32                     |
|:---------------|:------------------------|:------------------------|
| Addition       | 27,100,268,292,682,928  | 43,290,038,961,038,960  |
| BitAnd         | 42,735,038,461,538,464  | 44,247,783,185,840,704  |
| BitOr          | 44,247,783,185,840,704  | 44,444,440,000,000,000  |
| BitXor         | 44,247,783,185,840,704  | 44,444,440,000,000,000  |
| BitwiseNot     | 625,000,000,000,000,000 | 588,235,294,117,647,104 |
| ByteConversion | 666,666,666,666,666,752 | nan                     |
| Division       | 2,056,374,132           | 2,050,133,261           |
| FromI32        | 666,666,666,666,666,752 | nan                     |
| LeftShift      | 588,235,294,117,647,104 | 526,315,789,473,684,160 |
| Multiplication | 43,478,256,521,739,128  | 42,918,450,643,776,824  |
| Negation       | 588,235,294,117,647,104 | 666,666,666,666,666,752 |
| Remainder      | 863,742,668             | 2,473,845,159           |
| RightShift     | 500,000,000,000,000,000 | 555,555,555,555,555,584 |
| Subtraction    | 44,247,783,185,840,704  | 41,841,000,000,000,000  |
| ToI32          | 526,315,789,473,684,160 | nan                     |


### Duration (nanoseconds per operation)

| operation      |           i24 |           i32 |
|:---------------|--------------:|--------------:|
| Addition       | 369           | 231           |
| BitAnd         | 234           | 226           |
| BitOr          | 226           | 225           |
| BitXor         | 226           | 225           |
| BitwiseNot     |  16           |  17           |
| ByteConversion |  15           | nan           |
| Division       |   4.86293e+09 |   4.87773e+09 |
| FromI32        |  15           | nan           |
| LeftShift      |  17           |  19           |
| Multiplication | 230           | 233           |
| Negation       |  17           |  15           |
| Remainder      |   1.15775e+10 |   4.04229e+09 |
| RightShift     |  20           |  18           |
| Subtraction    | 226           | 239           |
| ToI32          |  19           | nan           |


### Relative Performance (i24 vs i32)

| Operation      | Throughput Ratio   | Duration Ratio   | Category   |
|:---------------|:-------------------|:-----------------|:-----------|
| Addition       | 0.63x              | 1.60x            | Arithmetic |
| BitAnd         | 0.97x              | 1.04x            | Bitwise    |
| BitOr          | 1.00x              | 1.00x            | Bitwise    |
| BitXor         | 1.00x              | 1.00x            | Bitwise    |
| BitwiseNot     | 1.06x              | 0.94x            | Bitwise    |
| ByteConversion | nan                | nan              | Conversion |
| Division       | 1.00x              | 1.00x            | Arithmetic |
| FromI32        | nan                | nan              | Conversion |
| LeftShift      | 1.12x              | 0.89x            | Shift      |
| Multiplication | 1.01x              | 0.99x            | Arithmetic |
| Negation       | 0.88x              | 1.13x            | Unary      |
| Remainder      | 0.35x              | 2.86x            | Arithmetic |
| RightShift     | 0.90x              | 1.11x            | Shift      |
| Subtraction    | 1.06x              | 0.95x            | Arithmetic |
| ToI32          | nan                | nan              | Conversion |


## Performance Highlights

### Top 5 Best Performers

| Operation      | Performance Ratio   | Category   |
|:---------------|:--------------------|:-----------|
| LeftShift      | 1.12x               | Shift      |
| BitwiseNot     | 1.06x               | Bitwise    |
| Subtraction    | 1.06x               | Arithmetic |
| Multiplication | 1.01x               | Arithmetic |
| Division       | 1.00x               | Arithmetic |


### Bottom 5 Worst Performers

| Operation   | Performance Ratio   | Category   |
|:------------|:--------------------|:-----------|
| Remainder   | 0.35x               | Arithmetic |
| Addition    | 0.63x               | Arithmetic |
| Negation    | 0.88x               | Unary      |
| RightShift  | 0.90x               | Shift      |
| BitAnd      | 0.97x               | Bitwise    |

