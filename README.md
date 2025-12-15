# Proof aggregator using recursive GKR scheme with Approximate Sum-Check
This is Cli tool for **generation of aggregated proof for multiple inputs**.

This implementation includes **Approximate Sum-Check Protocol** based on the paper ["Sum-Check Protocol for Approximate Computations"](https://eprint.iacr.org/2025/XXX) (2025).

In this version, it supports circom circuit.

## Paper Reference

**"Sum-Check Protocol for Approximate Computations"** (2025)

### Abstract
The standard sum-check protocol requires exact polynomial evaluations, which limits its applicability to computations with inherent approximation errors (e.g., floating-point arithmetic, machine learning inference). This work introduces an **approximate sum-check protocol** that tolerates bounded errors while maintaining soundness guarantees.

### Key Contributions
1. **Approximate Sum-Check Protocol**: Relaxes exact equality to bounded error tolerance
2. **Error Accumulation Analysis**: Proves that errors accumulate linearly across rounds
3. **Applications to FP Arithmetic**: Enables ZK proofs for IEEE 754 floating-point computations
4. **GKR Integration**: Extends the GKR protocol with approximate verification

### Theoretical Foundation
- **Standard Sum-Check**: $g_i(0) + g_i(1) = c_i$ (exact equality)
- **Approximate Sum-Check**: $|g_i(0) + g_i(1) - c_i| \leq \epsilon_i$ (bounded error)
- **Soundness**: If the prover cheats by more than $\sum_i \epsilon_i$, the verifier detects with high probability

## Approximate Sum-Check Protocol

### Overview
The standard sum-check protocol requires exact equality:
- **Standard:** `g_i(0) + g_i(1) = c_i`

The approximate sum-check allows bounded error tolerance:
- **Approximate:** `|g_i(0) + g_i(1) - c_i| <= epsilon_i`

### Key Features
- **Per-round error bounds (delta_i):** The prover sends error bounds along with each polynomial
- **Error accumulation tracking:** Total error is bounded by sum of per-round deltas
- **Backward compatibility:** Setting epsilon=0 gives exact verification

### Usage

#### Python
```python
from sumcheck import prove_approx_sumcheck, verify_approx_sumcheck, ApproxSumcheckProof
from gkr import prove_approx, verify_approx

# Approximate sumcheck with error tolerance
epsilon = field.FQ(100)  # Maximum error per round
approx_proof = prove_approx_sumcheck(g, num_vars, start_idx, max_delta=epsilon)
is_valid, accumulated_error = verify_approx_sumcheck(claim, approx_proof, num_vars)

# Approximate GKR
proof = prove_approx(circuit, D, max_delta=epsilon)
is_valid, total_error = verify_approx(proof)

# Standard exact verification (backward compatible)
proof = prove(circuit, D)
is_valid = verify(proof)
```

#### Rust
```rust
use gkr::sumcheck::{prove_approx_sumcheck, verify_approx_sumcheck, ApproxSumcheckProof};

// Approximate sumcheck
let max_delta = S::from(100u64);
let approx_proof = prove_approx_sumcheck(&g, v, max_delta);
let result = verify_approx_sumcheck(claim, &approx_proof, v, None);

// Standard exact verification
let (proof, r) = prove_sumcheck(&g, v);
let valid = verify_sumcheck(claim, &proof, &r, v);
```

#### Circom
```circom
// Standard exact sumcheck verification
component verify = SumcheckVerify(v, nTerms);

// Approximate sumcheck verification
component approxVerify = ApproxSumcheckVerify(v, nTerms);
approxVerify.deltas <== deltas;      // Per-round error bounds
approxVerify.errorSigns <== signs;   // Sign hints for absolute value
```

## IEEE 754 Floating Point Arithmetization

This implementation includes **IEEE 754 Floating Point Arithmetization** using GKR with approximate sumcheck. This is ideal for verifying floating point computations where rounding errors are inherent.

### Features

- **IEEE 754 Single & Double Precision** representation
- **FP Operations**: Add, Sub, Mul, Div, Sqrt with error bounds
- **ULP-based error computation** for accurate tolerance
- **Automatic error accumulation** across circuit layers
- **Circuit builders** for common operations (dot product, sum, matrix multiply)

### Usage

#### Python
```python
from fp_arithmetic import IEEE754Float, FPAddGate, FPMulGate
from fp_gkr import fp_prove_computation, verify_fp_gkr

# Prove a dot product computation
a = [1.0, 2.0, 3.0, 4.0]
b = [0.5, 1.5, 2.5, 3.5]
expected = sum(x * y for x, y in zip(a, b))  # 35.0

proof = fp_prove_computation('dot_product', a + b)
valid, info = verify_fp_gkr(proof, [expected])

print(f"Valid: {valid}, Max ULP error: {info['max_ulp_error']}")

# Other operations
sum_proof = fp_prove_computation('sum', [1.0, 2.0, 3.0, 4.0])
product_proof = fp_prove_computation('product', [1.1, 2.2, 3.3])
```

#### Rust
```rust
use fp_arithmetic::{IEEE754Float, fp_add, fp_mul, create_dot_product_circuit};

// Create and evaluate a dot product circuit
let mut circuit = create_dot_product_circuit::<Fr>(4);
circuit.set_inputs(&[1.0, 2.0, 3.0, 4.0, 0.5, 1.5, 2.5, 3.5]);
let outputs = circuit.evaluate();

println!("Result: {}", outputs[0].to_f32());
println!("Error bound: {:?}", circuit.total_epsilon);
```

#### Circom
```circom
include "fp/ieee754.circom";

// Verify FP dot product
component dotProduct = FPDotProductVerify(4, 5);
dotProduct.a_signs <== a_signs;
dotProduct.a_exps <== a_exps;
dotProduct.a_mants <== a_mants;
// ... etc
```

### Error Model

The error tolerance is computed based on IEEE 754 ULP (Unit in Last Place):
- **Addition/Subtraction**: 0.5 ULP per operation
- **Multiplication/Division**: 0.5 ULP per operation
- **Total Error**: Accumulated across all operations

The approximate sumcheck accepts proofs where:
`|computed - expected| <= total_epsilon`

## Benchmarking

### Quick Start
```sh
# Setup Python environment
cd python
python3 -m venv ../.venv
source ../.venv/bin/activate
pip install -r requirements.txt  # or just run the scripts (uses local field module)

# Run comprehensive FP GKR benchmark
python benchmark_fp_gkr.py

# Run aggregated proof benchmark
python benchmark_aggregated.py

# Run tests
python test_fp_gkr.py
python test_gkr.py
```

### Benchmark Results (M3 Max, 2024, 48GB RAM, 16 cores, 40 GPUs)

#### Single Operation Scaling
| Operation | Inputs | Prove Time | Verify Time | Proof Size | 
|-----------|--------|------------|-------------|------------|
| sum | 16 | ~5ms | ~5ms | 1.5KB |
| sum | 64 | ~16ms | ~10ms | 3.2KB |
| sum | 256 | ~110ms | ~19ms | 6.0KB |
| dot_product | 32 | ~9ms | ~7ms | 2.3KB |
| dot_product | 128 | ~38ms | ~15ms | 4.4KB |
| dot_product | 512 | ~396ms | ~24ms | 8.3KB |

#### Batch Aggregation Performance
| Batch Size | Input Size | Total Prove | Throughput |
|------------|------------|-------------|------------|
| 100 | 16 | ~560ms | ~92 proofs/s |
| 100 | 32 | ~925ms | ~59 proofs/s |
| 100 | 64 | ~1.7s | ~36 proofs/s |
| 200 | 32 | ~1.9s | ~58 proofs/s |

#### Real-World Scenarios
| Scenario | Proofs | Total Time | Size | Throughput |
|----------|--------|------------|------|------------|
| ML Inference (100 dot products) | 100 | ~2.8s | 319KB | 36 p/s |
| Financial (200 sums) | 200 | ~3.4s | 451KB | 59 p/s |
| IoT Sensors (100 mixed) | 100 | ~1.1s | 152KB | 92 p/s |

### Benchmark Scripts

#### `benchmark_fp_gkr.py`
Comprehensive benchmark covering:
- Single operation scaling (4-512 inputs)
- Batch proof aggregation
- Large-scale stress tests (up to 1024 inputs)
- Numerical accuracy analysis

#### `benchmark_aggregated.py`
Real-world aggregated proof scenarios:
- Mixed operation batches
- ML inference simulation (neural network layers)
- Financial computation batches
- IoT sensor data aggregation

### Running Custom Benchmarks
```python
from fp_gkr import fp_prove_computation, verify_fp_gkr
import time

# Benchmark custom computation
inputs = [float(i) for i in range(64)]
start = time.perf_counter()
proof = fp_prove_computation('sum', inputs)
prove_time = time.perf_counter() - start

start = time.perf_counter()
valid, info = verify_fp_gkr(proof, [sum(inputs)])
verify_time = time.perf_counter() - start

print(f"Prove: {prove_time*1000:.1f}ms, Verify: {verify_time*1000:.1f}ms")
```

## Preliminaries
circom and snarkjs should be installed already.

You can check that by this command:
```sh
snarkjs --help
```
```sh
circom --help
```
## How to use
### 1. Install gkr
```sh
cargo install --path ./rust
```
### 2. Move to `./rust`
```sh
cd rust
```
### 3. Write a circuit in `./rust` and inputs in `./rust/example/` (`/example` is not mandatory)

### 4. Create GKR proof for inputs
You can give inputs by commands:
```sh
gkr-aggregator prove -c circuit.circom -i ./example/input1.json ./example/input2.json ./example/input3.json
```

You can get a message from cli:
```sh
Proving by groth16 can be done
```

### 4. Prepare zkey
You should prepare an appropriate ptau file.
```sh
snarkjs groth16 setup aggregated.r1cs pot.ptau c0.zkey
snarkjs zkey contribute c0.zkey c1.zkey --name=“mock” -v
```
Give random string for contribution, and then
```sh
snarkjs zkey beacon c1.zkey c.zkey 0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f 10 -n="Final Beacon phase2"
```

### 5. Create aggregated Groth16 proof
```sh
gkr-aggregator mock-groth -z c.zkey
```
You can get `proof.json` and `public.json`.

## Implementation details
### Internal
#### Initial round
Get input from `input.json`, make `d` in proof with it.  
Parse r1cs file and convert it to `GKRCircuit`. (Let's call this $C$)  
Make proof $\pi_0$ from `d` and `GKRCircuit`.
#### Iterative round (0 < $i$ < n)
There are two circuit $C_i$ and $C_{v_{i - 1}}$. $C_{v_{i - 1}}$ is circuit that can verify $C_{i - 1}$.  
$C_{v_i}$ can be different form for each circuit $C_i$. 
To make aggregated proof for previous proof and current round's proof, we need
- input (for $C_i$)
- proof $\pi_{i - 1}$

Make integrated circuit $C'_i$.

Use those inputs, make proof $\pi_i$.
To be specific, input and proof $\pi_{i - 1}$
#### Last round
Also there are two circuit $C_n$ and $C_{v_{n - 1}}$. To send aggregated proof to on-chain verifier, we can use groth16 prover in `snarkjs`.  
Integrated circuit $C'_{n}$ can be proved with `snarkjs` also.  
So final proof $\pi_n$ is groth16 or plonk proof

## Project Structure

```
gkr-approx-sumcheck/
├── python/
│   ├── sumcheck.py          # Approximate sumcheck protocol
│   ├── gkr.py               # GKR protocol with approx support
│   ├── fp_arithmetic.py     # IEEE 754 FP arithmetization
│   ├── fp_gkr.py            # FP GKR prover/verifier
│   ├── benchmark_fp_gkr.py  # Comprehensive benchmarks
│   ├── benchmark_aggregated.py  # Aggregated proof benchmarks
│   ├── test_fp_gkr.py       # FP GKR tests
│   └── test_gkr.py          # Original GKR tests
├── rust/
│   └── src/
│       ├── gkr/
│       │   ├── sumcheck.rs  # Rust approx sumcheck
│       │   └── prover.rs    # GKR prover
│       └── fp_arithmetic.rs # Rust FP implementation
├── gkr-verifier-circuits/
│   └── circom/
│       └── circom/
│           ├── sumcheck/
│           │   └── sumcheckVerify.circom  # Approx sumcheck circuit
│           └── fp/
│               └── ieee754.circom  # FP verification circuits
└── README.md
```

## License
MIT
