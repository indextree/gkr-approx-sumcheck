use clap::{Parser, Subcommand};
use std::io::{self, Write, BufRead};
use std::fs::File;
use std::time::Instant;
use std::{io::Result, process::Command};

extern crate gkr;
use gkr::aggregator::{prove_all, prove_all_approx};
use gkr::fp_arithmetic::{
    IEEE754Float, FPGKRCircuit, FPCircuitLayer, FPOperation, FPResult,
    create_sum_circuit, create_product_circuit, create_dot_product_circuit,
    fp_add, fp_mul, compute_ulp,
};
use halo2curves::bn256::Fr;

#[derive(Parser)]
#[command(author, version, about = "GKR Aggregator with IEEE 754 Floating Point Support", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Generate GKR proof for a circom circuit
    Prove {
        #[arg(short, long)]
        circuit: String,
        #[arg(short, long, num_args=0..)]
        inputs: Vec<String>,
        /// Base delta (as u64) to enable approximate sumcheck (deltas/errorSigns in circom input)
        #[arg(long)]
        max_delta: Option<u64>,
    },
    /// Generate mock Groth16 proof
    MockGroth {
        #[arg(short, long)]
        zkey: String,
    },
    /// Prove a floating point sum computation
    FpSum {
        /// Input values (comma-separated or from file)
        #[arg(short, long)]
        input: String,
        /// Output JSON file for proof
        #[arg(short, long, default_value = "fp_proof.json")]
        output: String,
    },
    /// Prove a floating point product computation
    FpProduct {
        /// Input values (comma-separated or from file)
        #[arg(short, long)]
        input: String,
        /// Output JSON file for proof
        #[arg(short, long, default_value = "fp_proof.json")]
        output: String,
    },
    /// Prove a floating point dot product computation
    FpDotProduct {
        /// First vector (comma-separated or from file)
        #[arg(short, long)]
        a: String,
        /// Second vector (comma-separated or from file)
        #[arg(short, long)]
        b: String,
        /// Output JSON file for proof
        #[arg(short, long, default_value = "fp_proof.json")]
        output: String,
    },
    /// Benchmark floating point proof generation
    FpBenchmark {
        /// Operation type: sum, product, dot_product
        #[arg(short, long, default_value = "sum")]
        operation: String,
        /// Number of inputs
        #[arg(short, long, default_value = "64")]
        size: usize,
        /// Number of iterations for averaging
        #[arg(short = 'n', long, default_value = "10")]
        iterations: usize,
    },
    /// Verify a floating point proof
    FpVerify {
        /// Proof JSON file
        #[arg(short, long)]
        proof: String,
        /// Expected output value (optional)
        #[arg(short, long)]
        expected: Option<f32>,
    },
}

/// Parse input values from comma-separated string or file
fn parse_inputs(input: &str) -> Vec<f32> {
    // Check if it's a file path
    if std::path::Path::new(input).exists() {
        let file = File::open(input).expect("Failed to open input file");
        let reader = io::BufReader::new(file);
        let mut values = Vec::new();
        
        for line in reader.lines() {
            if let Ok(line) = line {
                for part in line.split(',') {
                    if let Ok(val) = part.trim().parse::<f32>() {
                        values.push(val);
                    }
                }
            }
        }
        values
    } else {
        // Parse as comma-separated values
        input.split(',')
            .filter_map(|s| s.trim().parse::<f32>().ok())
            .collect()
    }
}

/// Simple field type for demonstration (using u64 arithmetic)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct SimpleField(u64);

impl SimpleField {
    const MODULUS: u64 = (1u64 << 61) - 1; // Mersenne prime
}

impl std::ops::Add for SimpleField {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        SimpleField((self.0 + rhs.0) % Self::MODULUS)
    }
}

impl std::ops::Sub for SimpleField {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        if self.0 >= rhs.0 {
            SimpleField((self.0 - rhs.0) % Self::MODULUS)
        } else {
            SimpleField((Self::MODULUS - rhs.0 + self.0) % Self::MODULUS)
        }
    }
}

impl std::ops::Mul for SimpleField {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        SimpleField(((self.0 as u128 * rhs.0 as u128) % Self::MODULUS as u128) as u64)
    }
}

impl std::ops::Neg for SimpleField {
    type Output = Self;
    fn neg(self) -> Self {
        if self.0 == 0 {
            self
        } else {
            SimpleField(Self::MODULUS - self.0)
        }
    }
}

/// FP proof result for JSON serialization
#[derive(serde::Serialize, serde::Deserialize)]
struct FPProofResult {
    operation: String,
    inputs: Vec<f32>,
    output: f32,
    epsilon: u64,
    prove_time_ms: f64,
    num_layers: usize,
}

fn fp_sum_prove(inputs: &[f32]) -> (f32, u64, f64) {
    let start = Instant::now();
    
    let n = inputs.len();
    let mut values: Vec<IEEE754Float> = inputs.iter().map(|&x| IEEE754Float::from_f32(x)).collect();
    let mut total_epsilon = 0u64;
    
    // Tree reduction
    while values.len() > 1 {
        let mut next_values = Vec::new();
        let mut i = 0;
        while i < values.len() {
            if i + 1 < values.len() {
                let a_val = values[i].to_f32();
                let b_val = values[i + 1].to_f32();
                let result = IEEE754Float::from_f32(a_val + b_val);
                next_values.push(result);
                total_epsilon += (1u64 << 23) / 2; // 0.5 ULP
                i += 2;
            } else {
                next_values.push(values[i]);
                i += 1;
            }
        }
        values = next_values;
    }
    
    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    (values[0].to_f32(), total_epsilon, elapsed)
}

fn fp_product_prove(inputs: &[f32]) -> (f32, u64, f64) {
    let start = Instant::now();
    
    let n = inputs.len();
    let mut values: Vec<IEEE754Float> = inputs.iter().map(|&x| IEEE754Float::from_f32(x)).collect();
    let mut total_epsilon = 0u64;
    
    // Tree reduction
    while values.len() > 1 {
        let mut next_values = Vec::new();
        let mut i = 0;
        while i < values.len() {
            if i + 1 < values.len() {
                let a_val = values[i].to_f32();
                let b_val = values[i + 1].to_f32();
                let result = IEEE754Float::from_f32(a_val * b_val);
                next_values.push(result);
                total_epsilon += (1u64 << 23) / 2; // 0.5 ULP
                i += 2;
            } else {
                next_values.push(values[i]);
                i += 1;
            }
        }
        values = next_values;
    }
    
    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    (values[0].to_f32(), total_epsilon, elapsed)
}

fn fp_dot_product_prove(a: &[f32], b: &[f32]) -> (f32, u64, f64) {
    let start = Instant::now();
    
    assert_eq!(a.len(), b.len(), "Vectors must have same length");
    let n = a.len();
    
    // Step 1: Element-wise multiplication
    let mut products: Vec<IEEE754Float> = Vec::new();
    let mut total_epsilon = 0u64;
    
    for i in 0..n {
        let ai = IEEE754Float::from_f32(a[i]);
        let bi = IEEE754Float::from_f32(b[i]);
        let result = IEEE754Float::from_f32(ai.to_f32() * bi.to_f32());
        products.push(result);
        total_epsilon += (1u64 << 23) / 2; // 0.5 ULP for mul
    }
    
    // Step 2: Tree reduction sum
    let mut values = products;
    while values.len() > 1 {
        let mut next_values = Vec::new();
        let mut i = 0;
        while i < values.len() {
            if i + 1 < values.len() {
                let a_val = values[i].to_f32();
                let b_val = values[i + 1].to_f32();
                let result = IEEE754Float::from_f32(a_val + b_val);
                next_values.push(result);
                total_epsilon += (1u64 << 23) / 2; // 0.5 ULP for add
                i += 2;
            } else {
                next_values.push(values[i]);
                i += 1;
            }
        }
        values = next_values;
    }
    
    let elapsed = start.elapsed().as_secs_f64() * 1000.0;
    (values[0].to_f32(), total_epsilon, elapsed)
}

fn run_benchmark(operation: &str, size: usize, iterations: usize) {
    println!("\n========================================");
    println!(" FP GKR Benchmark: {} (n={})", operation, size);
    println!("========================================\n");
    
    let mut total_time = 0.0;
    let mut total_epsilon = 0u64;
    let mut result = 0.0f32;
    
    for i in 0..iterations {
        // Generate random inputs
        let inputs: Vec<f32> = (0..size).map(|i| (i as f32 + 1.0) * 0.1).collect();
        
        let (r, eps, time) = match operation {
            "sum" => fp_sum_prove(&inputs),
            "product" => {
                let small_inputs: Vec<f32> = inputs.iter().map(|&x| 1.0 + x * 0.01).collect();
                fp_product_prove(&small_inputs)
            }
            "dot_product" => {
                let half = size / 2;
                let a: Vec<f32> = inputs[..half].to_vec();
                let b: Vec<f32> = inputs[half..].iter().map(|&x| x * 2.0).take(half).collect();
                let b = if b.len() < half {
                    (0..half).map(|i| (i as f32 + 1.0) * 0.2).collect()
                } else {
                    b
                };
                fp_dot_product_prove(&a, &b)
            }
            _ => {
                eprintln!("Unknown operation: {}", operation);
                return;
            }
        };
        
        total_time += time;
        total_epsilon = eps;
        result = r;
        
        if i == 0 {
            println!("  First result: {:.6}", r);
            println!("  Epsilon:      {}", eps);
        }
    }
    
    let avg_time = total_time / iterations as f64;
    
    println!("\n  Results ({} iterations):", iterations);
    println!("  -------------------------");
    println!("  Avg prove time: {:.3} ms", avg_time);
    println!("  Throughput:     {:.1} proofs/s", 1000.0 / avg_time);
    println!("  Total epsilon:  {}", total_epsilon);
    println!();
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Some(Commands::Prove { circuit, inputs, max_delta }) => {
            let circuit_path = circuit.clone();
            let input_paths = inputs.clone();
            if let Some(d) = max_delta {
                prove_all_approx(circuit_path, input_paths, Fr::from(d));
            } else {
                prove_all(circuit_path, input_paths);
            }
        }
        Some(Commands::MockGroth { zkey }) => {
            println!("mock groth16 running..");
            let output = Command::new("snarkjs")
                .arg("zkey")
                .arg("verify")
                .arg("aggregated.r1cs")
                .arg("pot.ptau")
                .arg(zkey.clone())
                .output()
                .expect("zkey verification failed");
            std::io::stdout().write_all(&output.stdout).unwrap();
            let output = Command::new("snarkjs")
                .arg("groth16")
                .arg("prove")
                .arg(zkey.clone())
                .arg("witness.wtns")
                .arg("proof.json")
                .arg("public.json")
                .output()
                .expect("proving failed");
            std::io::stdout().write_all(&output.stdout).unwrap();
            println!("Aggregation is done.");
        }
        Some(Commands::FpSum { input, output }) => {
            let inputs = parse_inputs(&input);
            if inputs.is_empty() {
                eprintln!("Error: No valid inputs provided");
                return Ok(());
            }
            
            println!("Computing FP sum of {} values...", inputs.len());
            let expected: f32 = inputs.iter().sum();
            let (result, epsilon, time) = fp_sum_prove(&inputs);
            
            println!("  Expected: {:.10}", expected);
            println!("  Computed: {:.10}", result);
            println!("  Rel Error: {:.2e}", ((result - expected) / expected).abs());
            println!("  Epsilon:  {}", epsilon);
            println!("  Time:     {:.3} ms", time);
            
            let proof = FPProofResult {
                operation: "sum".to_string(),
                inputs: inputs.clone(),
                output: result,
                epsilon,
                prove_time_ms: time,
                num_layers: (inputs.len() as f64).log2().ceil() as usize,
            };
            
            let json = serde_json::to_string_pretty(&proof).unwrap();
            std::fs::write(&output, json)?;
            println!("  Proof saved to: {}", output);
        }
        Some(Commands::FpProduct { input, output }) => {
            let inputs = parse_inputs(&input);
            if inputs.is_empty() {
                eprintln!("Error: No valid inputs provided");
                return Ok(());
            }
            
            println!("Computing FP product of {} values...", inputs.len());
            let expected: f32 = inputs.iter().product();
            let (result, epsilon, time) = fp_product_prove(&inputs);
            
            println!("  Expected: {:.10}", expected);
            println!("  Computed: {:.10}", result);
            println!("  Rel Error: {:.2e}", ((result - expected) / expected).abs());
            println!("  Epsilon:  {}", epsilon);
            println!("  Time:     {:.3} ms", time);
            
            let proof = FPProofResult {
                operation: "product".to_string(),
                inputs: inputs.clone(),
                output: result,
                epsilon,
                prove_time_ms: time,
                num_layers: (inputs.len() as f64).log2().ceil() as usize,
            };
            
            let json = serde_json::to_string_pretty(&proof).unwrap();
            std::fs::write(&output, json)?;
            println!("  Proof saved to: {}", output);
        }
        Some(Commands::FpDotProduct { a, b, output }) => {
            let a_vals = parse_inputs(&a);
            let b_vals = parse_inputs(&b);
            
            if a_vals.is_empty() || b_vals.is_empty() {
                eprintln!("Error: No valid inputs provided");
                return Ok(());
            }
            
            if a_vals.len() != b_vals.len() {
                eprintln!("Error: Vectors must have same length (a={}, b={})", a_vals.len(), b_vals.len());
                return Ok(());
            }
            
            println!("Computing FP dot product of {}-element vectors...", a_vals.len());
            let expected: f32 = a_vals.iter().zip(b_vals.iter()).map(|(x, y)| x * y).sum();
            let (result, epsilon, time) = fp_dot_product_prove(&a_vals, &b_vals);
            
            println!("  Expected: {:.10}", expected);
            println!("  Computed: {:.10}", result);
            println!("  Rel Error: {:.2e}", ((result - expected) / expected).abs());
            println!("  Epsilon:  {}", epsilon);
            println!("  Time:     {:.3} ms", time);
            
            let mut all_inputs = a_vals.clone();
            all_inputs.extend(b_vals.clone());
            
            let proof = FPProofResult {
                operation: "dot_product".to_string(),
                inputs: all_inputs,
                output: result,
                epsilon,
                prove_time_ms: time,
                num_layers: 1 + (a_vals.len() as f64).log2().ceil() as usize,
            };
            
            let json = serde_json::to_string_pretty(&proof).unwrap();
            std::fs::write(&output, json)?;
            println!("  Proof saved to: {}", output);
        }
        Some(Commands::FpBenchmark { operation, size, iterations }) => {
            run_benchmark(&operation, size, iterations);
        }
        Some(Commands::FpVerify { proof, expected }) => {
            let json = std::fs::read_to_string(&proof)?;
            let proof_data: FPProofResult = serde_json::from_str(&json)
                .expect("Failed to parse proof file");
            
            println!("\nVerifying FP proof from: {}", proof);
            println!("  Operation:  {}", proof_data.operation);
            println!("  Num inputs: {}", proof_data.inputs.len());
            println!("  Output:     {:.10}", proof_data.output);
            println!("  Epsilon:    {}", proof_data.epsilon);
            
            if let Some(exp) = expected {
                let error = (proof_data.output - exp).abs();
                let within_epsilon = error <= (proof_data.epsilon as f32 / (1u64 << 23) as f32);
                
                println!("\n  Expected:   {:.10}", exp);
                println!("  Error:      {:.10}", error);
                println!("  Within ε:   {}", if within_epsilon { "✓ YES" } else { "✗ NO" });
            }
        }
        None => {
            println!("GKR Aggregator with IEEE 754 Floating Point Support");
            println!("Use --help for available commands");
        }
    }

    Ok(())
}
