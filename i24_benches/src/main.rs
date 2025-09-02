use i24::{I24, U24, i24, u24};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::time::Instant;

// Define the operations we want to benchmark
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
enum Operation {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Neg,
    Not,
    FromI32,
    ToI32,
    ToU32,
    FromU32,
    ByteConversion,
}

impl std::fmt::Display for Operation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operation::Add => write!(f, "Addition"),
            Operation::Sub => write!(f, "Subtraction"),
            Operation::Mul => write!(f, "Multiplication"),
            Operation::Div => write!(f, "Division"),
            Operation::Rem => write!(f, "Remainder"),
            Operation::BitAnd => write!(f, "BitAnd"),
            Operation::BitOr => write!(f, "BitOr"),
            Operation::BitXor => write!(f, "BitXor"),
            Operation::Shl => write!(f, "LeftShift"),
            Operation::Shr => write!(f, "RightShift"),
            Operation::Neg => write!(f, "Negation"),
            Operation::Not => write!(f, "BitwiseNot"),
            Operation::FromI32 => write!(f, "FromI32"),
            Operation::ToI32 => write!(f, "ToI32"),
            Operation::ToU32 => write!(f, "ToU32"),
            Operation::FromU32 => write!(f, "FromU32"),
            Operation::ByteConversion => write!(f, "ByteConversion"),
        }
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct BenchmarkResult {
    operation: String,
    operand_type: String,
    iterations: usize,
    duration_ns: u128,
    throughput: f64, // Operations per second
}

#[derive(Debug, Serialize, Deserialize)]
struct BenchmarkSuite {
    timestamp: String,
    system_info: SystemInfo,
    results: Vec<BenchmarkResult>,
}

#[derive(Debug, Serialize, Deserialize)]
struct SystemInfo {
    cpu_info: String,
    memory_mb: u64,
    os: String,
    rust_version: String,
}

// Generate random I24 values within the valid range
fn generate_i24_values(count: usize, seed: u64) -> Vec<I24> {
    let mut rng = StdRng::seed_from_u64(seed);
    let range = I24::MIN.to_i32()..=I24::MAX.to_i32();

    (0..count)
        .map(|_| {
            let value = rng.random_range(range.clone());
            I24::try_from_i32(value).unwrap_or(i24!(0))
        })
        .collect()
}

// Generate random U24 values within the valid range
fn generate_u24_values(count: usize, seed: u64) -> Vec<U24> {
    let mut rng = StdRng::seed_from_u64(seed);
    let range = U24::MIN.to_u32()..=U24::MAX.to_u32();

    (0..count)
        .map(|_| {
            let value = rng.random_range(range.clone());
            U24::try_from_u32(value).unwrap_or(u24!(0))
        })
        .collect()
}

// Generate random i32 values for comparison
fn generate_i32_values(count: usize, seed: u64) -> Vec<i32> {
    let mut rng = StdRng::seed_from_u64(seed);
    // Use the same range as I24 for fairness
    let range = I24::MIN.to_i32()..=I24::MAX.to_i32();

    (0..count)
        .map(|_| rng.random_range(range.clone()))
        .collect()
}

// Generate random u32 values for U24 comparison
fn generate_u32_values(count: usize, seed: u64) -> Vec<u32> {
    let mut rng = StdRng::seed_from_u64(seed);
    // Use the same range as U24 for fairness
    let range = U24::MIN.to_u32()..=U24::MAX.to_u32();

    (0..count)
        .map(|_| rng.random_range(range.clone()))
        .collect()
}

// Generate random shift amounts (u32) for shift operations
fn generate_shift_values(count: usize, seed: u64) -> Vec<u32> {
    let mut rng = StdRng::seed_from_u64(seed);
    let range = 0..24; // Limit shifts to I24::BITS

    (0..count)
        .map(|_| rng.random_range(range.clone()))
        .collect()
}

// Benchmark a binary operation on I24 values
fn bench_binary_op<F>(
    op: Operation,
    values: &[I24],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(I24, I24) -> I24,
{
    // Warmup
    let mut result = i24!(0);
    for i in 0..values.len() - 1 {
        result = op_func(values[i], values[i + 1]);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() - 1 {
            result = op_func(values[i], values[i + 1]);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = (values.len() - 1) * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "I24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a binary operation on U24 values
fn bench_binary_op_u24<F>(
    op: Operation,
    values: &[U24],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(U24, U24) -> U24,
{
    // Warmup
    let mut result = u24!(0);
    for i in 0..values.len() - 1 {
        result = op_func(values[i], values[i + 1]);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() - 1 {
            result = op_func(values[i], values[i + 1]);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = (values.len() - 1) * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "U24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a binary operation on i32 values for comparison
fn bench_binary_op_i32<F>(
    op: Operation,
    values: &[i32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(i32, i32) -> i32,
{
    // Warmup
    let mut result = 0i32;
    for i in 0..values.len() - 1 {
        result = op_func(values[i], values[i + 1]);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() - 1 {
            result = op_func(values[i], values[i + 1]);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = (values.len() - 1) * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "i32".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a binary operation on u32 values for U24 comparison
fn bench_binary_op_u32<F>(
    op: Operation,
    values: &[u32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(u32, u32) -> u32,
{
    // Warmup
    let mut result = 0u32;
    for i in 0..values.len() - 1 {
        result = op_func(values[i], values[i + 1]);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() - 1 {
            result = op_func(values[i], values[i + 1]);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = (values.len() - 1) * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "u32".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a unary operation on I24 values
fn bench_unary_op<F>(
    op: Operation,
    values: &[I24],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(I24) -> I24,
{
    // Warmup
    let mut result = i24!(0);
    for val in values {
        result = op_func(*val);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = op_func(*val);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the results
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "I24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a unary operation on U24 values
fn bench_unary_op_u24<F>(
    op: Operation,
    values: &[U24],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(U24) -> U24,
{
    // Warmup
    let mut result = u24!(0);
    for val in values {
        result = op_func(*val);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = op_func(*val);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the results
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "U24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a unary operation on i32 values for comparison
fn bench_unary_op_i32<F>(
    op: Operation,
    values: &[i32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(i32) -> i32,
{
    // Warmup
    let mut result = 0i32;
    for val in values {
        result = op_func(*val);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = op_func(*val);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the results
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "i32".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a unary operation on u32 values for U24 comparison
fn bench_unary_op_u32<F>(
    op: Operation,
    values: &[u32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(u32) -> u32,
{
    // Warmup
    let mut result = 0u32;
    for val in values {
        result = op_func(*val);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = op_func(*val);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the results
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "u32".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a shift operation on I24 values
fn bench_shift_op<F>(
    op: Operation,
    values: &[I24],
    shift_amounts: &[u32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(I24, u32) -> I24,
{
    // Warmup
    let mut result = i24!(0);
    for i in 0..values.len() {
        let shift = shift_amounts[i % shift_amounts.len()];
        result = op_func(values[i], shift);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() {
            let shift = shift_amounts[i % shift_amounts.len()];
            result = op_func(values[i], shift);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "I24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a shift operation on U24 values
fn bench_shift_op_u24<F>(
    op: Operation,
    values: &[U24],
    shift_amounts: &[u32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(U24, u32) -> U24,
{
    // Warmup
    let mut result = u24!(0);
    for i in 0..values.len() {
        let shift = shift_amounts[i % shift_amounts.len()];
        result = op_func(values[i], shift);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() {
            let shift = shift_amounts[i % shift_amounts.len()];
            result = op_func(values[i], shift);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "U24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a shift operation on i32 values for comparison
fn bench_shift_op_i32<F>(
    op: Operation,
    values: &[i32],
    shift_amounts: &[u32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(i32, u32) -> i32,
{
    // Warmup
    let mut result = 0i32;
    for i in 0..values.len() {
        let shift = shift_amounts[i % shift_amounts.len()];
        result = op_func(values[i], shift);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() {
            let shift = shift_amounts[i % shift_amounts.len()];
            result = op_func(values[i], shift);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "i32".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark a shift operation on u32 values for U24 comparison
fn bench_shift_op_u32<F>(
    op: Operation,
    values: &[u32],
    shift_amounts: &[u32],
    op_func: F,
    iterations: usize,
) -> BenchmarkResult
where
    F: Fn(u32, u32) -> u32,
{
    // Warmup
    let mut result = 0u32;
    for i in 0..values.len() {
        let shift = shift_amounts[i % shift_amounts.len()];
        result = op_func(values[i], shift);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for i in 0..values.len() {
            let shift = shift_amounts[i % shift_amounts.len()];
            result = op_func(values[i], shift);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: op.to_string(),
        operand_type: "u32".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark conversions
fn bench_i24_to_i32(values: &[I24], iterations: usize) -> BenchmarkResult {
    // Warmup
    let mut result = 0i32;
    for val in values {
        result = val.to_i32();
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = val.to_i32();
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: Operation::ToI32.to_string(),
        operand_type: "I24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

fn bench_i32_to_i24(values: &[i32], iterations: usize) -> BenchmarkResult {
    // Warmup
    let mut result = i24!(0);
    for val in values {
        result = I24::wrapping_from_i32(*val);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = I24::wrapping_from_i32(*val);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: Operation::FromI32.to_string(),
        operand_type: "I24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

fn bench_u24_to_u32(values: &[U24], iterations: usize) -> BenchmarkResult {
    // Warmup
    let mut result = 0u32;
    for val in values {
        result = val.to_u32();
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = val.to_u32();
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: "ToU32".to_string(),
        operand_type: "U24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

fn bench_u32_to_u24(values: &[u32], iterations: usize) -> BenchmarkResult {
    // Warmup
    let mut result = u24!(0);
    for val in values {
        result = U24::wrapping_from_u32(*val);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            result = U24::wrapping_from_u32(*val);
        }
    }
    let duration = start.elapsed();

    // Force the compiler to keep the result
    std::hint::black_box(result);

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());

    BenchmarkResult {
        operation: "FromU32".to_string(),
        operand_type: "U24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Benchmark byte conversion operations
fn bench_i24_byte_conversions(values: &[I24], iterations: usize) -> BenchmarkResult {
    // Warmup
    let mut bytes = [0u8; 3];
    for val in values {
        bytes = val.to_le_bytes();
        let _ = I24::from_le_bytes(bytes);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            bytes = val.to_le_bytes();
            let _ = I24::from_le_bytes(bytes);
        }
    }
    let duration = start.elapsed();

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());
    let _ = bytes; // Prevent unused variable warning
    BenchmarkResult {
        operation: Operation::ByteConversion.to_string(),
        operand_type: "I24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

fn bench_u24_byte_conversions(values: &[U24], iterations: usize) -> BenchmarkResult {
    // Warmup
    let mut bytes = [0u8; 3];
    for val in values {
        bytes = val.to_le_bytes();
        let _ = U24::from_le_bytes(bytes);
    }

    // Time it
    let start = Instant::now();
    for _ in 0..iterations {
        for val in values {
            bytes = val.to_le_bytes();
            let _ = U24::from_le_bytes(bytes);
        }
    }
    let duration = start.elapsed();

    let ops_count = values.len() * iterations;
    let throughput = ops_count as f64 / (duration.as_secs_f64());
    let _ = bytes; // Prevent unused variable warning
    BenchmarkResult {
        operation: Operation::ByteConversion.to_string(),
        operand_type: "U24".to_string(),
        iterations,
        duration_ns: duration.as_nanos(),
        throughput,
    }
}

// Run all benchmarks and return results
fn run_benchmarks(sample_size: usize, iterations: usize) -> BenchmarkSuite {
    // Generate test data
    let seed = 42; // Fixed seed for reproducibility
    let i24_values = generate_i24_values(sample_size, seed);
    let u24_values = generate_u24_values(sample_size, seed);
    let i32_values = generate_i32_values(sample_size, seed);
    let u32_values = generate_u32_values(sample_size, seed);
    let shift_values = generate_shift_values(sample_size, seed);

    let mut results = Vec::new();

    // Binary operations
    println!("Benchmarking binary operations...");

    // Addition
    results.push(bench_binary_op(
        Operation::Add,
        &i24_values,
        |a, b| a + b,
        iterations,
    ));

    results.push(bench_binary_op_i32(
        Operation::Add,
        &i32_values,
        |a, b| a + b,
        iterations,
    ));

    results.push(bench_binary_op_u24(
        Operation::Add,
        &u24_values,
        |a, b| a + b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::Add,
        &u32_values,
        |a, b| a + b,
        iterations,
    ));

    // Subtraction
    results.push(bench_binary_op(
        Operation::Sub,
        &i24_values,
        |a, b| a - b,
        iterations,
    ));
    results.push(bench_binary_op_i32(
        Operation::Sub,
        &i32_values,
        |a, b| a - b,
        iterations,
    ));
    results.push(bench_binary_op_u24(
        Operation::Sub,
        &u24_values,
        |a, b| a - b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::Sub,
        &u32_values,
        |a, b| a - b,
        iterations,
    ));

    // Multiplication
    results.push(bench_binary_op(
        Operation::Mul,
        &i24_values,
        |a, b| a * b,
        iterations,
    ));
    results.push(bench_binary_op_i32(
        Operation::Mul,
        &i32_values,
        |a, b| a * b,
        iterations,
    ));
    results.push(bench_binary_op_u24(
        Operation::Mul,
        &u24_values,
        |a, b| a * b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::Mul,
        &u32_values,
        |a, b| a * b,
        iterations,
    ));

    // Division
    // Filter out zeros to avoid division by zero
    let div_i24_values: Vec<I24> = i24_values
        .iter()
        .filter(|&x| *x != i24!(0))
        .cloned()
        .collect();
    let div_u24_values: Vec<U24> = u24_values
        .iter()
        .filter(|&x| *x != u24!(0))
        .cloned()
        .collect();
    let div_i32_values: Vec<i32> = i32_values.iter().filter(|&x| *x != 0).cloned().collect();
    let div_u32_values: Vec<u32> = u32_values.iter().filter(|&x| *x != 0).cloned().collect();

    results.push(bench_binary_op(
        Operation::Div,
        &div_i24_values,
        |a, b| a / b,
        iterations,
    ));
    results.push(bench_binary_op_i32(
        Operation::Div,
        &div_i32_values,
        |a, b| a / b,
        iterations,
    ));
    results.push(bench_binary_op_u24(
        Operation::Div,
        &div_u24_values,
        |a, b| a / b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::Div,
        &div_u32_values,
        |a, b| a / b,
        iterations,
    ));

    // Remainder
    results.push(bench_binary_op(
        Operation::Rem,
        &div_i24_values,
        |a, b| a % b,
        iterations,
    ));
    results.push(bench_binary_op_i32(
        Operation::Rem,
        &div_i32_values,
        |a, b| a % b,
        iterations,
    ));
    results.push(bench_binary_op_u24(
        Operation::Rem,
        &div_u24_values,
        |a, b| a % b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::Rem,
        &div_u32_values,
        |a, b| a % b,
        iterations,
    ));

    // Bitwise operations
    results.push(bench_binary_op(
        Operation::BitAnd,
        &i24_values,
        |a, b| a & b,
        iterations,
    ));
    results.push(bench_binary_op_i32(
        Operation::BitAnd,
        &i32_values,
        |a, b| a & b,
        iterations,
    ));
    results.push(bench_binary_op_u24(
        Operation::BitAnd,
        &u24_values,
        |a, b| a & b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::BitAnd,
        &u32_values,
        |a, b| a & b,
        iterations,
    ));

    results.push(bench_binary_op(
        Operation::BitOr,
        &i24_values,
        |a, b| a | b,
        iterations,
    ));
    results.push(bench_binary_op_i32(
        Operation::BitOr,
        &i32_values,
        |a, b| a | b,
        iterations,
    ));
    results.push(bench_binary_op_u24(
        Operation::BitOr,
        &u24_values,
        |a, b| a | b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::BitOr,
        &u32_values,
        |a, b| a | b,
        iterations,
    ));

    results.push(bench_binary_op(
        Operation::BitXor,
        &i24_values,
        |a, b| a ^ b,
        iterations,
    ));
    results.push(bench_binary_op_i32(
        Operation::BitXor,
        &i32_values,
        |a, b| a ^ b,
        iterations,
    ));
    results.push(bench_binary_op_u24(
        Operation::BitXor,
        &u24_values,
        |a, b| a ^ b,
        iterations,
    ));
    results.push(bench_binary_op_u32(
        Operation::BitXor,
        &u32_values,
        |a, b| a ^ b,
        iterations,
    ));

    // Shift operations
    println!("Benchmarking shift operations...");
    results.push(bench_shift_op(
        Operation::Shl,
        &i24_values,
        &shift_values,
        |a, s| a << s,
        iterations,
    ));
    results.push(bench_shift_op_i32(
        Operation::Shl,
        &i32_values,
        &shift_values,
        |a, s| a << s,
        iterations,
    ));
    results.push(bench_shift_op_u24(
        Operation::Shl,
        &u24_values,
        &shift_values,
        |a, s| a << s,
        iterations,
    ));
    results.push(bench_shift_op_u32(
        Operation::Shl,
        &u32_values,
        &shift_values,
        |a, s| a << s,
        iterations,
    ));

    results.push(bench_shift_op(
        Operation::Shr,
        &i24_values,
        &shift_values,
        |a, s| a >> s,
        iterations,
    ));
    results.push(bench_shift_op_i32(
        Operation::Shr,
        &i32_values,
        &shift_values,
        |a, s| a >> s,
        iterations,
    ));
    results.push(bench_shift_op_u24(
        Operation::Shr,
        &u24_values,
        &shift_values,
        |a, s| a >> s,
        iterations,
    ));
    results.push(bench_shift_op_u32(
        Operation::Shr,
        &u32_values,
        &shift_values,
        |a, s| a >> s,
        iterations,
    ));

    // Unary operations
    println!("Benchmarking unary operations...");
    results.push(bench_unary_op(
        Operation::Neg,
        &i24_values,
        |a| -a,
        iterations,
    ));
    results.push(bench_unary_op_i32(
        Operation::Neg,
        &i32_values,
        |a| -a,
        iterations,
    ));

    // Note: U24 doesn't support negation (unsigned), so we skip that

    results.push(bench_unary_op(
        Operation::Not,
        &i24_values,
        |a| !a,
        iterations,
    ));
    results.push(bench_unary_op_i32(
        Operation::Not,
        &i32_values,
        |a| !a,
        iterations,
    ));
    results.push(bench_unary_op_u24(
        Operation::Not,
        &u24_values,
        |a| !a,
        iterations,
    ));
    results.push(bench_unary_op_u32(
        Operation::Not,
        &u32_values,
        |a| !a,
        iterations,
    ));

    // Conversion operations
    println!("Benchmarking conversions...");
    results.push(bench_i24_to_i32(&i24_values, iterations));
    results.push(bench_i32_to_i24(&i32_values, iterations));
    results.push(bench_u24_to_u32(&u24_values, iterations));
    results.push(bench_u32_to_u24(&u32_values, iterations));

    // Byte conversion operations
    println!("Benchmarking byte conversions...");
    results.push(bench_i24_byte_conversions(&i24_values, iterations));
    results.push(bench_u24_byte_conversions(&u24_values, iterations));

    // Create benchmark suite with system info
    BenchmarkSuite {
        timestamp: chrono::Local::now().to_rfc3339(),
        system_info: get_system_info(),
        results,
    }
}

// Get basic system information
fn get_system_info() -> SystemInfo {
    SystemInfo {
        cpu_info: sys_info::cpu_num()
            .map(|n| format!("{} cores", n))
            .unwrap_or_else(|_| "Unknown".to_string()),
        memory_mb: sys_info::mem_info().map(|m| m.total / 1024).unwrap_or(0),
        os: format!(
            "{} {}",
            sys_info::os_type().unwrap_or_else(|_| "Unknown".to_string()),
            sys_info::os_release().unwrap_or_else(|_| "Unknown".to_string())
        ),
        rust_version: rustc_version_runtime::version().to_string(),
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Configure benchmark parameters
    let sample_size = 10_000_000;
    let iterations = 1_000;

    println!("Starting I24 benchmarks");
    println!("Sample size: {}, Iterations: {}", sample_size, iterations);

    // Run benchmarks
    let benchmark_suite = run_benchmarks(sample_size, iterations);

    // Write results to JSON file
    let file = File::create("I24_benchmark_results.json")?;
    serde_json::to_writer_pretty(file, &benchmark_suite)?;

    println!("Benchmarks complete. Results written to I24_benchmark_results.json");

    // Print summary to console
    println!("\nSummary:");
    println!(
        "{:<15} {:<10} {:<15} {:<15}",
        "Operation", "Type", "Duration (ms)", "Ops/sec"
    );
    println!("{}", "-".repeat(60));

    for result in &benchmark_suite.results {
        println!(
            "{:<15} {:<10} {:<15.2} {:<15.0}",
            result.operation,
            result.operand_type,
            result.duration_ns as f64 / 1_000_000.0,
            result.throughput
        );
    }

    Ok(())
}
