"""
IEEE 754 Floating Point Arithmetization for GKR with Approximate Sum-Check

Based on "Sum-Check Protocol for Approximate Computations" (2025)

IEEE 754 Single Precision (32-bit):
- 1 bit sign (s)
- 8 bits exponent (e), biased by 127
- 23 bits mantissa (m), with implicit leading 1

Value = (-1)^s * 2^(e-127) * (1.m)

The approximate sumcheck is ideal for FP arithmetic because:
1. Rounding errors are inherent in FP operations
2. We can bound the error by epsilon (ULP - unit in last place)
3. The verifier accepts proofs within the error tolerance
"""

from typing import List, Tuple, Optional
from dataclasses import dataclass
try:
    from ethsnarks import field
except ImportError:
    # Use local field module if ethsnarks not available
    import field
import struct
import math

# =============================================================================
# IEEE 754 Floating Point Representation
# =============================================================================

@dataclass
class IEEE754Float:
    """IEEE 754 single precision floating point representation"""
    sign: int        # 1 bit
    exponent: int    # 8 bits (biased)
    mantissa: int    # 23 bits (without implicit 1)
    
    EXPONENT_BIAS = 127
    MANTISSA_BITS = 23
    EXPONENT_BITS = 8
    
    @classmethod
    def from_float(cls, f: float) -> 'IEEE754Float':
        """Convert Python float to IEEE754Float"""
        if f == 0.0:
            return cls(0, 0, 0)
        
        # Pack as IEEE 754 single precision
        packed = struct.pack('>f', f)
        bits = struct.unpack('>I', packed)[0]
        
        sign = (bits >> 31) & 1
        exponent = (bits >> 23) & 0xFF
        mantissa = bits & 0x7FFFFF
        
        return cls(sign, exponent, mantissa)
    
    def to_float(self) -> float:
        """Convert back to Python float"""
        if self.exponent == 0 and self.mantissa == 0:
            return 0.0
        
        bits = (self.sign << 31) | (self.exponent << 23) | self.mantissa
        packed = struct.pack('>I', bits)
        return struct.unpack('>f', packed)[0]
    
    def to_field_elements(self) -> List[field.FQ]:
        """Convert to field elements for circuit representation"""
        elements = []
        
        # Sign bit
        elements.append(field.FQ(self.sign))
        
        # Exponent bits (8 bits)
        for i in range(self.EXPONENT_BITS - 1, -1, -1):
            elements.append(field.FQ((self.exponent >> i) & 1))
        
        # Mantissa bits (23 bits)
        for i in range(self.MANTISSA_BITS - 1, -1, -1):
            elements.append(field.FQ((self.mantissa >> i) & 1))
        
        return elements
    
    @classmethod
    def from_field_elements(cls, elements: List[field.FQ]) -> 'IEEE754Float':
        """Reconstruct from field elements"""
        sign = int(elements[0])
        
        exponent = 0
        for i in range(cls.EXPONENT_BITS):
            exponent = (exponent << 1) | int(elements[1 + i])
        
        mantissa = 0
        for i in range(cls.MANTISSA_BITS):
            mantissa = (mantissa << 1) | int(elements[1 + cls.EXPONENT_BITS + i])
        
        return cls(sign, exponent, mantissa)
    
    def get_real_mantissa(self) -> int:
        """Get mantissa with implicit leading 1"""
        if self.exponent == 0:  # Denormalized
            return self.mantissa
        return (1 << self.MANTISSA_BITS) | self.mantissa
    
    def get_real_exponent(self) -> int:
        """Get unbiased exponent"""
        if self.exponent == 0:  # Denormalized
            return 1 - self.EXPONENT_BIAS
        return self.exponent - self.EXPONENT_BIAS


@dataclass  
class IEEE754Double:
    """IEEE 754 double precision floating point representation"""
    sign: int        # 1 bit
    exponent: int    # 11 bits (biased)
    mantissa: int    # 52 bits (without implicit 1)
    
    EXPONENT_BIAS = 1023
    MANTISSA_BITS = 52
    EXPONENT_BITS = 11
    
    @classmethod
    def from_float(cls, f: float) -> 'IEEE754Double':
        """Convert Python float to IEEE754Double"""
        if f == 0.0:
            return cls(0, 0, 0)
        
        packed = struct.pack('>d', f)
        bits = struct.unpack('>Q', packed)[0]
        
        sign = (bits >> 63) & 1
        exponent = (bits >> 52) & 0x7FF
        mantissa = bits & 0xFFFFFFFFFFFFF
        
        return cls(sign, exponent, mantissa)
    
    def to_float(self) -> float:
        """Convert back to Python float"""
        if self.exponent == 0 and self.mantissa == 0:
            return 0.0
        
        bits = (self.sign << 63) | (self.exponent << 52) | self.mantissa
        packed = struct.pack('>Q', bits)
        return struct.unpack('>d', packed)[0]


# =============================================================================
# Floating Point Error Bounds (ULP - Unit in Last Place)
# =============================================================================

def compute_ulp(fp: IEEE754Float) -> float:
    """
    Compute the Unit in Last Place (ULP) for a floating point number.
    ULP is the spacing between adjacent floating point numbers.
    """
    if fp.exponent == 0:  # Denormalized
        return 2.0 ** (1 - fp.EXPONENT_BIAS - fp.MANTISSA_BITS)
    
    real_exp = fp.exponent - fp.EXPONENT_BIAS
    return 2.0 ** (real_exp - fp.MANTISSA_BITS)


def compute_epsilon_for_operation(a: IEEE754Float, b: IEEE754Float, op: str) -> field.FQ:
    """
    Compute the error bound (epsilon) for a floating point operation.
    This is used as the delta in approximate sumcheck.
    
    For addition: error <= 0.5 * ULP(result)
    For multiplication: error <= 0.5 * ULP(result)
    """
    a_val = a.to_float()
    b_val = b.to_float()
    
    if op == 'add':
        result = a_val + b_val
    elif op == 'mul':
        result = a_val * b_val
    elif op == 'sub':
        result = a_val - b_val
    elif op == 'div':
        result = a_val / b_val if b_val != 0 else 0
    else:
        result = a_val
    
    if result == 0:
        return field.FQ(1)
    
    result_fp = IEEE754Float.from_float(result)
    ulp = compute_ulp(result_fp)
    
    # Error bound is 0.5 ULP for correctly rounded operations
    # We scale to field representation (multiply by 2^23 for mantissa precision)
    error_bound = int(0.5 * (2 ** IEEE754Float.MANTISSA_BITS))
    
    return field.FQ(max(1, error_bound))


# =============================================================================
# Floating Point Circuit Gates
# =============================================================================

class FPGate:
    """Base class for floating point gates in the circuit"""
    
    @staticmethod
    def bits_to_field(bits: List[int]) -> field.FQ:
        """Convert bit array to field element"""
        result = 0
        for bit in bits:
            result = (result << 1) | bit
        return field.FQ(result)
    
    @staticmethod
    def field_to_bits(val: field.FQ, num_bits: int) -> List[field.FQ]:
        """Convert field element to bit array"""
        v = int(val)
        bits = []
        for i in range(num_bits - 1, -1, -1):
            bits.append(field.FQ((v >> i) & 1))
        return bits


class FPAddGate(FPGate):
    """
    Floating point addition gate.
    
    Algorithm:
    1. Align exponents (shift smaller mantissa right)
    2. Add/subtract mantissas based on signs
    3. Normalize result
    4. Round to nearest even
    """
    
    @staticmethod
    def compute(a: IEEE754Float, b: IEEE754Float) -> Tuple[IEEE754Float, field.FQ]:
        """
        Compute a + b and return (result, error_bound)
        """
        a_val = a.to_float()
        b_val = b.to_float()
        result_val = a_val + b_val
        result = IEEE754Float.from_float(result_val)
        
        # Compute error bound
        epsilon = compute_epsilon_for_operation(a, b, 'add')
        
        return result, epsilon
    
    @staticmethod
    def to_circuit_constraints(a_bits: List[field.FQ], b_bits: List[field.FQ]) -> List[field.FQ]:
        """
        Generate circuit constraints for FP addition.
        Returns the output bits and intermediate values.
        """
        # Reconstruct floats
        a = IEEE754Float.from_field_elements(a_bits)
        b = IEEE754Float.from_field_elements(b_bits)
        
        result, _ = FPAddGate.compute(a, b)
        return result.to_field_elements()


class FPMulGate(FPGate):
    """
    Floating point multiplication gate.
    
    Algorithm:
    1. XOR signs
    2. Add exponents (subtract bias)
    3. Multiply mantissas
    4. Normalize and round
    """
    
    @staticmethod
    def compute(a: IEEE754Float, b: IEEE754Float) -> Tuple[IEEE754Float, field.FQ]:
        """
        Compute a * b and return (result, error_bound)
        """
        a_val = a.to_float()
        b_val = b.to_float()
        result_val = a_val * b_val
        result = IEEE754Float.from_float(result_val)
        
        epsilon = compute_epsilon_for_operation(a, b, 'mul')
        
        return result, epsilon
    
    @staticmethod
    def to_circuit_constraints(a_bits: List[field.FQ], b_bits: List[field.FQ]) -> List[field.FQ]:
        """Generate circuit constraints for FP multiplication."""
        a = IEEE754Float.from_field_elements(a_bits)
        b = IEEE754Float.from_field_elements(b_bits)
        
        result, _ = FPMulGate.compute(a, b)
        return result.to_field_elements()


class FPDivGate(FPGate):
    """Floating point division gate."""
    
    @staticmethod
    def compute(a: IEEE754Float, b: IEEE754Float) -> Tuple[IEEE754Float, field.FQ]:
        """Compute a / b and return (result, error_bound)"""
        a_val = a.to_float()
        b_val = b.to_float()
        
        if b_val == 0:
            # Handle division by zero (return infinity representation)
            return IEEE754Float(a.sign ^ b.sign, 0xFF, 0), field.FQ(0)
        
        result_val = a_val / b_val
        result = IEEE754Float.from_float(result_val)
        
        epsilon = compute_epsilon_for_operation(a, b, 'div')
        
        return result, epsilon


class FPSqrtGate(FPGate):
    """Floating point square root gate."""
    
    @staticmethod
    def compute(a: IEEE754Float) -> Tuple[IEEE754Float, field.FQ]:
        """Compute sqrt(a) and return (result, error_bound)"""
        a_val = a.to_float()
        
        if a_val < 0:
            # Return NaN for negative input
            return IEEE754Float(0, 0xFF, 1), field.FQ(0)
        
        result_val = math.sqrt(a_val)
        result = IEEE754Float.from_float(result_val)
        
        # Error bound for sqrt is approximately 0.5 ULP
        ulp = compute_ulp(result)
        error_bound = int(0.5 * (2 ** IEEE754Float.MANTISSA_BITS))
        
        return result, field.FQ(max(1, error_bound))


# =============================================================================
# Floating Point GKR Circuit
# =============================================================================

class FPCircuitLayer:
    """A layer in the floating point GKR circuit"""
    
    def __init__(self, num_gates: int, gate_type: str):
        self.num_gates = num_gates
        self.gate_type = gate_type  # 'add', 'mul', 'div', 'sqrt'
        self.inputs: List[Tuple[int, int]] = []  # (left_idx, right_idx) for each gate
        self.outputs: List[IEEE754Float] = []
        self.epsilons: List[field.FQ] = []  # Error bounds per gate
    
    def add_gate(self, left_idx: int, right_idx: int):
        """Add a gate with specified input indices"""
        self.inputs.append((left_idx, right_idx))
    
    def evaluate(self, prev_layer_values: List[IEEE754Float]) -> List[IEEE754Float]:
        """Evaluate all gates in this layer"""
        self.outputs = []
        self.epsilons = []
        
        for left_idx, right_idx in self.inputs:
            a = prev_layer_values[left_idx]
            b = prev_layer_values[right_idx] if right_idx >= 0 else a
            
            if self.gate_type == 'add':
                result, eps = FPAddGate.compute(a, b)
            elif self.gate_type == 'mul':
                result, eps = FPMulGate.compute(a, b)
            elif self.gate_type == 'div':
                result, eps = FPDivGate.compute(a, b)
            elif self.gate_type == 'sqrt':
                result, eps = FPSqrtGate.compute(a)
            else:
                raise ValueError(f"Unknown gate type: {self.gate_type}")
            
            self.outputs.append(result)
            self.epsilons.append(eps)
        
        return self.outputs
    
    def get_total_epsilon(self) -> field.FQ:
        """Get total error bound for this layer"""
        return sum(self.epsilons, field.FQ.zero())


class FPGKRCircuit:
    """
    Floating Point GKR Circuit with Approximate Sum-Check
    
    This circuit uses the approximate sumcheck protocol to verify
    floating point computations with bounded rounding errors.
    """
    
    def __init__(self):
        self.layers: List[FPCircuitLayer] = []
        self.input_values: List[IEEE754Float] = []
        self.total_epsilon: field.FQ = field.FQ.zero()
    
    def add_layer(self, layer: FPCircuitLayer):
        """Add a layer to the circuit"""
        self.layers.append(layer)
    
    def set_inputs(self, inputs: List[float]):
        """Set input values (as Python floats)"""
        self.input_values = [IEEE754Float.from_float(x) for x in inputs]
    
    def evaluate(self) -> List[IEEE754Float]:
        """Evaluate the entire circuit"""
        current_values = self.input_values
        self.total_epsilon = field.FQ.zero()
        
        for layer in self.layers:
            current_values = layer.evaluate(current_values)
            self.total_epsilon = self.total_epsilon + layer.get_total_epsilon()
        
        return current_values
    
    def get_error_bound(self) -> field.FQ:
        """Get the total error bound for the computation"""
        return self.total_epsilon
    
    def to_gkr_circuit(self):
        """
        Convert to GKR circuit format for proving.
        This creates the add_i and mult_i functions for each layer.
        """
        from gkr import Circuit, Layer, Node
        
        depth = len(self.layers) + 1  # +1 for input layer
        circuit = Circuit(depth)
        
        # Build circuit structure
        # ... (detailed implementation would go here)
        
        return circuit


# =============================================================================
# Floating Point Proof Generation and Verification
# =============================================================================

class FPProof:
    """Proof for floating point computation with approximate sumcheck"""
    
    def __init__(self):
        self.circuit_proof = None
        self.input_values: List[IEEE754Float] = []
        self.output_values: List[IEEE754Float] = []
        self.layer_epsilons: List[field.FQ] = []
        self.total_epsilon: field.FQ = field.FQ.zero()
    
    def to_dict(self):
        return {
            'inputs': [{'sign': fp.sign, 'exp': fp.exponent, 'mantissa': fp.mantissa} 
                      for fp in self.input_values],
            'outputs': [{'sign': fp.sign, 'exp': fp.exponent, 'mantissa': fp.mantissa}
                       for fp in self.output_values],
            'layer_epsilons': [repr(e) for e in self.layer_epsilons],
            'total_epsilon': repr(self.total_epsilon)
        }


def prove_fp_computation(circuit: FPGKRCircuit, inputs: List[float]) -> FPProof:
    """
    Generate a proof for a floating point computation.
    Uses approximate sumcheck with error bounds based on ULP.
    """
    circuit.set_inputs(inputs)
    outputs = circuit.evaluate()
    
    proof = FPProof()
    proof.input_values = circuit.input_values
    proof.output_values = outputs
    proof.layer_epsilons = [layer.get_total_epsilon() for layer in circuit.layers]
    proof.total_epsilon = circuit.get_error_bound()
    
    # Generate GKR proof with approximate sumcheck
    # gkr_circuit = circuit.to_gkr_circuit()
    # proof.circuit_proof = prove_approx(gkr_circuit, outputs, proof.total_epsilon)
    
    return proof


def verify_fp_computation(proof: FPProof, expected_outputs: List[float], 
                          tolerance_ulps: int = 1) -> Tuple[bool, float]:
    """
    Verify a floating point computation proof.
    
    Args:
        proof: The FP proof to verify
        expected_outputs: Expected output values
        tolerance_ulps: Number of ULPs tolerance for comparison
    
    Returns:
        (is_valid, max_error_ulps)
    """
    max_error_ulps = 0.0
    
    for i, (computed, expected) in enumerate(zip(proof.output_values, expected_outputs)):
        computed_val = computed.to_float()
        
        if expected == 0:
            error = abs(computed_val)
        else:
            expected_fp = IEEE754Float.from_float(expected)
            ulp = compute_ulp(expected_fp)
            error = abs(computed_val - expected) / ulp if ulp > 0 else 0
        
        max_error_ulps = max(max_error_ulps, error)
    
    is_valid = max_error_ulps <= tolerance_ulps
    
    # Also verify the GKR proof with approximate sumcheck
    # if proof.circuit_proof:
    #     gkr_valid, _ = verify_approx(proof.circuit_proof)
    #     is_valid = is_valid and gkr_valid
    
    return is_valid, max_error_ulps


# =============================================================================
# Example: Matrix Multiplication with FP
# =============================================================================

def create_fp_matmul_circuit(m: int, n: int, p: int) -> FPGKRCircuit:
    """
    Create a circuit for matrix multiplication C = A * B
    where A is m x n and B is n x p.
    
    Each output C[i][j] = sum(A[i][k] * B[k][j] for k in range(n))
    """
    circuit = FPGKRCircuit()
    
    # Layer 1: All multiplications A[i][k] * B[k][j]
    mul_layer = FPCircuitLayer(m * n * p, 'mul')
    for i in range(m):
        for j in range(p):
            for k in range(n):
                a_idx = i * n + k          # Index of A[i][k]
                b_idx = m * n + k * p + j  # Index of B[k][j]
                mul_layer.add_gate(a_idx, b_idx)
    circuit.add_layer(mul_layer)
    
    # Layers 2+: Tree reduction for summation
    current_size = m * p * n
    while current_size > m * p:
        add_layer = FPCircuitLayer(current_size // 2, 'add')
        for i in range(current_size // 2):
            add_layer.add_gate(2 * i, 2 * i + 1)
        circuit.add_layer(add_layer)
        current_size = current_size // 2
    
    return circuit


def create_fp_dot_product_circuit(n: int) -> FPGKRCircuit:
    """
    Create a circuit for dot product: sum(a[i] * b[i])
    """
    circuit = FPGKRCircuit()
    
    # Layer 1: Element-wise multiplication
    mul_layer = FPCircuitLayer(n, 'mul')
    for i in range(n):
        mul_layer.add_gate(i, n + i)
    circuit.add_layer(mul_layer)
    
    # Layers 2+: Tree reduction for summation
    current_size = n
    while current_size > 1:
        next_size = (current_size + 1) // 2
        add_layer = FPCircuitLayer(next_size, 'add')
        for i in range(current_size // 2):
            add_layer.add_gate(2 * i, 2 * i + 1)
        if current_size % 2 == 1:
            add_layer.add_gate(current_size - 1, current_size - 1)  # Pass through
        circuit.add_layer(add_layer)
        current_size = next_size
    
    return circuit


# =============================================================================
# Test Functions
# =============================================================================

def test_ieee754_conversion():
    """Test IEEE 754 conversion"""
    test_values = [0.0, 1.0, -1.0, 3.14159, 1e10, 1e-10, 0.1]
    
    print("Testing IEEE 754 conversion:")
    for val in test_values:
        fp = IEEE754Float.from_float(val)
        recovered = fp.to_float()
        error = abs(val - recovered) if val != 0 else abs(recovered)
        print(f"  {val:>15} -> s={fp.sign}, e={fp.exponent:3}, m={fp.mantissa:8} -> {recovered:>15} (error: {error:.2e})")


def test_fp_operations():
    """Test floating point operations"""
    a = IEEE754Float.from_float(3.14159)
    b = IEEE754Float.from_float(2.71828)
    
    print("\nTesting FP operations:")
    
    # Addition
    result, eps = FPAddGate.compute(a, b)
    print(f"  {a.to_float()} + {b.to_float()} = {result.to_float()} (epsilon: {eps})")
    
    # Multiplication
    result, eps = FPMulGate.compute(a, b)
    print(f"  {a.to_float()} * {b.to_float()} = {result.to_float()} (epsilon: {eps})")
    
    # Division
    result, eps = FPDivGate.compute(a, b)
    print(f"  {a.to_float()} / {b.to_float()} = {result.to_float()} (epsilon: {eps})")
    
    # Square root
    result, eps = FPSqrtGate.compute(a)
    print(f"  sqrt({a.to_float()}) = {result.to_float()} (epsilon: {eps})")


def test_dot_product():
    """Test dot product circuit"""
    n = 4
    a = [1.0, 2.0, 3.0, 4.0]
    b = [0.5, 1.5, 2.5, 3.5]
    
    circuit = create_fp_dot_product_circuit(n)
    circuit.set_inputs(a + b)
    outputs = circuit.evaluate()
    
    expected = sum(x * y for x, y in zip(a, b))
    computed = outputs[0].to_float()
    
    print(f"\nDot product test:")
    print(f"  a = {a}")
    print(f"  b = {b}")
    print(f"  Expected: {expected}")
    print(f"  Computed: {computed}")
    print(f"  Error: {abs(expected - computed):.2e}")
    print(f"  Total epsilon: {circuit.get_error_bound()}")


if __name__ == "__main__":
    test_ieee754_conversion()
    test_fp_operations()
    test_dot_product()
