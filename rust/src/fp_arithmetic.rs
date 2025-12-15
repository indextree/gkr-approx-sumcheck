//! IEEE 754 Floating Point Arithmetization for GKR with Approximate Sum-Check
//!
//! Based on "Sum-Check Protocol for Approximate Computations" (2025)
//!
//! This module provides:
//! - IEEE 754 single/double precision representation
//! - Floating point gate implementations (add, mul, div, sqrt)
//! - Error bound computation (ULP-based)
//! - Integration with approximate sumcheck GKR

use ff::PrimeField;
use std::ops::{Add, Mul, Sub, Div};

// =============================================================================
// IEEE 754 Floating Point Representation
// =============================================================================

/// IEEE 754 Single Precision (32-bit) floating point
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct IEEE754Float {
    pub sign: u8,       // 1 bit
    pub exponent: u8,   // 8 bits (biased)
    pub mantissa: u32,  // 23 bits (without implicit 1)
}

impl IEEE754Float {
    pub const EXPONENT_BIAS: i32 = 127;
    pub const MANTISSA_BITS: u32 = 23;
    pub const EXPONENT_BITS: u32 = 8;
    
    /// Create a new IEEE754Float
    pub fn new(sign: u8, exponent: u8, mantissa: u32) -> Self {
        Self { sign, exponent, mantissa }
    }
    
    /// Create from a Rust f32
    pub fn from_f32(f: f32) -> Self {
        if f == 0.0 {
            return Self::new(0, 0, 0);
        }
        
        let bits = f.to_bits();
        let sign = ((bits >> 31) & 1) as u8;
        let exponent = ((bits >> 23) & 0xFF) as u8;
        let mantissa = bits & 0x7FFFFF;
        
        Self::new(sign, exponent, mantissa)
    }
    
    /// Convert to Rust f32
    pub fn to_f32(&self) -> f32 {
        if self.exponent == 0 && self.mantissa == 0 {
            return if self.sign == 1 { -0.0 } else { 0.0 };
        }
        
        let bits = ((self.sign as u32) << 31) 
                 | ((self.exponent as u32) << 23) 
                 | self.mantissa;
        f32::from_bits(bits)
    }
    
    /// Get mantissa with implicit leading 1 (for normalized numbers)
    pub fn get_real_mantissa(&self) -> u32 {
        if self.exponent == 0 {
            // Denormalized number
            self.mantissa
        } else {
            (1 << Self::MANTISSA_BITS) | self.mantissa
        }
    }
    
    /// Get unbiased exponent
    pub fn get_real_exponent(&self) -> i32 {
        if self.exponent == 0 {
            1 - Self::EXPONENT_BIAS
        } else {
            (self.exponent as i32) - Self::EXPONENT_BIAS
        }
    }
    
    /// Check if this is zero
    pub fn is_zero(&self) -> bool {
        self.exponent == 0 && self.mantissa == 0
    }
    
    /// Check if this is infinity
    pub fn is_infinity(&self) -> bool {
        self.exponent == 0xFF && self.mantissa == 0
    }
    
    /// Check if this is NaN
    pub fn is_nan(&self) -> bool {
        self.exponent == 0xFF && self.mantissa != 0
    }
    
    /// Convert to field element using scaled representation
    pub fn to_field<S: PrimeField>(&self, scale_bits: u32) -> S {
        let val = self.to_f32() as f64;
        let scale = (1u64 << scale_bits) as f64;
        let scaled = (val * scale) as i64;
        
        if scaled >= 0 {
            S::from(scaled as u64)
        } else {
            S::zero() - S::from((-scaled) as u64)
        }
    }
    
    /// Create from field element
    pub fn from_field<S: PrimeField<Repr = [u8; 32]>>(f: S, scale_bits: u32) -> Self {
        let repr = f.to_repr();
        let mut val = 0i128;
        
        // Convert from little-endian bytes
        for (i, byte) in repr.as_ref().iter().enumerate().take(16) {
            val |= (*byte as i128) << (i * 8);
        }
        
        // Check if negative (high bit set in field representation)
        let is_neg = repr.as_ref()[31] > 127;
        if is_neg {
            // This is a simplified handling - proper implementation would
            // subtract from field modulus
            val = -val;
        }
        
        let scale = (1u64 << scale_bits) as f64;
        let float_val = (val as f64) / scale;
        
        Self::from_f32(float_val as f32)
    }
}

/// IEEE 754 Double Precision (64-bit) floating point
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct IEEE754Double {
    pub sign: u8,       // 1 bit
    pub exponent: u16,  // 11 bits (biased)
    pub mantissa: u64,  // 52 bits (without implicit 1)
}

impl IEEE754Double {
    pub const EXPONENT_BIAS: i32 = 1023;
    pub const MANTISSA_BITS: u32 = 52;
    pub const EXPONENT_BITS: u32 = 11;
    
    pub fn from_f64(f: f64) -> Self {
        if f == 0.0 {
            return Self { sign: 0, exponent: 0, mantissa: 0 };
        }
        
        let bits = f.to_bits();
        let sign = ((bits >> 63) & 1) as u8;
        let exponent = ((bits >> 52) & 0x7FF) as u16;
        let mantissa = bits & 0xFFFFFFFFFFFFF;
        
        Self { sign, exponent, mantissa }
    }
    
    pub fn to_f64(&self) -> f64 {
        if self.exponent == 0 && self.mantissa == 0 {
            return if self.sign == 1 { -0.0 } else { 0.0 };
        }
        
        let bits = ((self.sign as u64) << 63)
                 | ((self.exponent as u64) << 52)
                 | self.mantissa;
        f64::from_bits(bits)
    }
}

// =============================================================================
// Error Bound Computation (ULP - Unit in Last Place)
// =============================================================================

/// Compute the Unit in Last Place (ULP) for a floating point number
pub fn compute_ulp(fp: &IEEE754Float) -> f32 {
    if fp.exponent == 0 {
        // Denormalized number
        f32::from_bits(1) // Smallest positive denormal
    } else if fp.exponent == 0xFF {
        // Infinity or NaN
        f32::INFINITY
    } else {
        let exp = fp.exponent as i32 - IEEE754Float::EXPONENT_BIAS as i32;
        let ulp_exp = exp - IEEE754Float::MANTISSA_BITS as i32;
        2.0_f32.powi(ulp_exp)
    }
}

/// Compute error bound for a floating point operation
pub fn compute_epsilon_for_operation<S: PrimeField>(
    a: &IEEE754Float,
    b: &IEEE754Float,
    op: FPOperation,
) -> S {
    let a_val = a.to_f32();
    let b_val = b.to_f32();
    
    let result = match op {
        FPOperation::Add => a_val + b_val,
        FPOperation::Sub => a_val - b_val,
        FPOperation::Mul => a_val * b_val,
        FPOperation::Div => if b_val != 0.0 { a_val / b_val } else { 0.0 },
        FPOperation::Sqrt => a_val.sqrt(),
    };
    
    if result == 0.0 || result.is_nan() || result.is_infinite() {
        return S::one();
    }
    
    let result_fp = IEEE754Float::from_f32(result);
    let ulp = compute_ulp(&result_fp);
    
    // Error bound is 0.5 ULP for correctly rounded operations
    // Scale to integer representation
    let error_bound = (0.5 * (1u64 << IEEE754Float::MANTISSA_BITS) as f32) as u64;
    
    S::from(error_bound.max(1))
}

/// Floating point operation types
#[derive(Clone, Copy, Debug)]
pub enum FPOperation {
    Add,
    Sub,
    Mul,
    Div,
    Sqrt,
}

// =============================================================================
// Floating Point Gate Operations
// =============================================================================

/// Result of a floating point operation with error bound
#[derive(Clone, Debug)]
pub struct FPResult<S: PrimeField> {
    pub result: IEEE754Float,
    pub epsilon: S,
}

/// Floating point addition
pub fn fp_add<S: PrimeField>(a: &IEEE754Float, b: &IEEE754Float) -> FPResult<S> {
    let result = IEEE754Float::from_f32(a.to_f32() + b.to_f32());
    let epsilon = compute_epsilon_for_operation(a, b, FPOperation::Add);
    FPResult { result, epsilon }
}

/// Floating point subtraction
pub fn fp_sub<S: PrimeField>(a: &IEEE754Float, b: &IEEE754Float) -> FPResult<S> {
    let result = IEEE754Float::from_f32(a.to_f32() - b.to_f32());
    let epsilon = compute_epsilon_for_operation(a, b, FPOperation::Sub);
    FPResult { result, epsilon }
}

/// Floating point multiplication
pub fn fp_mul<S: PrimeField>(a: &IEEE754Float, b: &IEEE754Float) -> FPResult<S> {
    let result = IEEE754Float::from_f32(a.to_f32() * b.to_f32());
    let epsilon = compute_epsilon_for_operation(a, b, FPOperation::Mul);
    FPResult { result, epsilon }
}

/// Floating point division
pub fn fp_div<S: PrimeField>(a: &IEEE754Float, b: &IEEE754Float) -> FPResult<S> {
    let b_val = b.to_f32();
    let result = if b_val != 0.0 {
        IEEE754Float::from_f32(a.to_f32() / b_val)
    } else {
        // Division by zero - return infinity
        IEEE754Float::new(a.sign ^ b.sign, 0xFF, 0)
    };
    let epsilon = compute_epsilon_for_operation(a, b, FPOperation::Div);
    FPResult { result, epsilon }
}

/// Floating point square root
pub fn fp_sqrt<S: PrimeField>(a: &IEEE754Float) -> FPResult<S> {
    let a_val = a.to_f32();
    let result = if a_val >= 0.0 {
        IEEE754Float::from_f32(a_val.sqrt())
    } else {
        // Return NaN for negative input
        IEEE754Float::new(0, 0xFF, 1)
    };
    let epsilon = compute_epsilon_for_operation(a, a, FPOperation::Sqrt);
    FPResult { result, epsilon }
}

// =============================================================================
// Floating Point Circuit Layer
// =============================================================================

/// A layer in a floating point circuit
#[derive(Clone, Debug)]
pub struct FPCircuitLayer<S: PrimeField> {
    pub gate_type: FPOperation,
    pub connections: Vec<(usize, usize)>, // (left_idx, right_idx) for each gate
    pub outputs: Vec<IEEE754Float>,
    pub epsilons: Vec<S>,
}

impl<S: PrimeField> FPCircuitLayer<S> {
    pub fn new(gate_type: FPOperation) -> Self {
        Self {
            gate_type,
            connections: Vec::new(),
            outputs: Vec::new(),
            epsilons: Vec::new(),
        }
    }
    
    pub fn add_gate(&mut self, left_idx: usize, right_idx: usize) {
        self.connections.push((left_idx, right_idx));
    }
    
    pub fn evaluate(&mut self, prev_layer: &[IEEE754Float]) {
        self.outputs.clear();
        self.epsilons.clear();
        
        for &(left_idx, right_idx) in &self.connections {
            let a = &prev_layer[left_idx];
            let b = &prev_layer[right_idx];
            
            let result: FPResult<S> = match self.gate_type {
                FPOperation::Add => fp_add(a, b),
                FPOperation::Sub => fp_sub(a, b),
                FPOperation::Mul => fp_mul(a, b),
                FPOperation::Div => fp_div(a, b),
                FPOperation::Sqrt => fp_sqrt(a),
            };
            
            self.outputs.push(result.result);
            self.epsilons.push(result.epsilon);
        }
    }
    
    pub fn get_total_epsilon(&self) -> S {
        self.epsilons.iter().fold(S::zero(), |acc, e| acc + *e)
    }
}

// =============================================================================
// Floating Point GKR Circuit
// =============================================================================

/// Floating point GKR circuit with approximate sumcheck support
#[derive(Clone, Debug)]
pub struct FPGKRCircuit<S: PrimeField> {
    pub layers: Vec<FPCircuitLayer<S>>,
    pub input_values: Vec<IEEE754Float>,
    pub total_epsilon: S,
}

impl<S: PrimeField> FPGKRCircuit<S> {
    pub fn new() -> Self {
        Self {
            layers: Vec::new(),
            input_values: Vec::new(),
            total_epsilon: S::zero(),
        }
    }
    
    pub fn add_layer(&mut self, layer: FPCircuitLayer<S>) {
        self.layers.push(layer);
    }
    
    pub fn set_inputs(&mut self, inputs: &[f32]) {
        self.input_values = inputs.iter().map(|&x| IEEE754Float::from_f32(x)).collect();
    }
    
    pub fn evaluate(&mut self) -> Vec<IEEE754Float> {
        let mut current = self.input_values.clone();
        self.total_epsilon = S::zero();
        
        for layer in &mut self.layers {
            layer.evaluate(&current);
            current = layer.outputs.clone();
            self.total_epsilon = self.total_epsilon + layer.get_total_epsilon();
        }
        
        current
    }
    
    pub fn get_outputs(&self) -> Vec<IEEE754Float> {
        if let Some(last_layer) = self.layers.last() {
            last_layer.outputs.clone()
        } else {
            self.input_values.clone()
        }
    }
}

impl<S: PrimeField> Default for FPGKRCircuit<S> {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// Floating Point Proof Structure
// =============================================================================

/// Proof for floating point GKR computation
#[derive(Clone, Debug)]
pub struct FPGKRProof<S: PrimeField> {
    /// Input floating point values
    pub input_fps: Vec<IEEE754Float>,
    /// Output floating point values
    pub output_fps: Vec<IEEE754Float>,
    /// Per-layer error bounds
    pub layer_epsilons: Vec<S>,
    /// Total error bound
    pub total_epsilon: S,
    /// Sumcheck proofs for each layer
    pub sumcheck_proofs: Vec<Vec<Vec<S>>>,
    /// Random challenges
    pub sumcheck_r: Vec<Vec<S>>,
    /// Per-round deltas
    pub sumcheck_deltas: Vec<Vec<S>>,
}

// =============================================================================
// Circuit Builders for Common Operations
// =============================================================================

/// Create a circuit for dot product computation
pub fn create_dot_product_circuit<S: PrimeField>(n: usize) -> FPGKRCircuit<S> {
    let mut circuit = FPGKRCircuit::new();
    
    // Layer 1: Element-wise multiplication
    let mut mul_layer = FPCircuitLayer::new(FPOperation::Mul);
    for i in 0..n {
        mul_layer.add_gate(i, n + i);
    }
    circuit.add_layer(mul_layer);
    
    // Layers 2+: Tree reduction for sum
    let mut current_size = n;
    while current_size > 1 {
        let mut add_layer = FPCircuitLayer::new(FPOperation::Add);
        for i in 0..(current_size / 2) {
            add_layer.add_gate(2 * i, 2 * i + 1);
        }
        if current_size % 2 == 1 {
            add_layer.add_gate(current_size - 1, current_size - 1);
        }
        circuit.add_layer(add_layer);
        current_size = (current_size + 1) / 2;
    }
    
    circuit
}

/// Create a circuit for sum computation
pub fn create_sum_circuit<S: PrimeField>(n: usize) -> FPGKRCircuit<S> {
    let mut circuit = FPGKRCircuit::new();
    
    let mut current_size = n;
    while current_size > 1 {
        let mut add_layer = FPCircuitLayer::new(FPOperation::Add);
        for i in 0..(current_size / 2) {
            add_layer.add_gate(2 * i, 2 * i + 1);
        }
        if current_size % 2 == 1 {
            add_layer.add_gate(current_size - 1, current_size - 1);
        }
        circuit.add_layer(add_layer);
        current_size = (current_size + 1) / 2;
    }
    
    circuit
}

/// Create a circuit for product computation
pub fn create_product_circuit<S: PrimeField>(n: usize) -> FPGKRCircuit<S> {
    let mut circuit = FPGKRCircuit::new();
    
    let mut current_size = n;
    while current_size > 1 {
        let mut mul_layer = FPCircuitLayer::new(FPOperation::Mul);
        for i in 0..(current_size / 2) {
            mul_layer.add_gate(2 * i, 2 * i + 1);
        }
        if current_size % 2 == 1 {
            mul_layer.add_gate(current_size - 1, current_size - 1);
        }
        circuit.add_layer(mul_layer);
        current_size = (current_size + 1) / 2;
    }
    
    circuit
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    
    // Use a simple field for testing
    type TestField = ff::PrimeField;
    
    #[test]
    fn test_ieee754_conversion() {
        let test_values = [0.0f32, 1.0, -1.0, 3.14159, 1e10, 1e-10, 0.1];
        
        for &val in &test_values {
            let fp = IEEE754Float::from_f32(val);
            let recovered = fp.to_f32();
            
            if val == 0.0 {
                assert!(recovered == 0.0);
            } else {
                let rel_error = ((val - recovered) / val).abs();
                assert!(rel_error < 1e-6, "Value {} recovered as {} with error {}", val, recovered, rel_error);
            }
        }
    }
    
    #[test]
    fn test_ulp_computation() {
        let fp = IEEE754Float::from_f32(1.0);
        let ulp = compute_ulp(&fp);
        
        // ULP of 1.0 should be 2^-23 ≈ 1.19e-7
        assert!(ulp > 1e-8 && ulp < 1e-6);
    }
}
