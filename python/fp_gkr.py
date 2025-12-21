"""
IEEE 754 Floating Point GKR Prover and Verifier

This module integrates the floating point arithmetization with the
approximate sumcheck-based GKR protocol.
"""

from typing import List, Tuple, Optional, Dict, Any
from dataclasses import dataclass
try:
    from ethsnarks import field
except ImportError:
    import field
import math

from fp_arithmetic import (
    IEEE754Float, IEEE754Double, FPGKRCircuit, FPCircuitLayer,
    FPAddGate, FPMulGate, FPDivGate, FPSqrtGate,
    compute_ulp, compute_epsilon_for_operation
)
from gkr import Circuit, Layer, Node, Proof, ApproxProof, prove, prove_approx, verify, verify_approx
from sumcheck import ApproxSumcheckProof, prove_approx_sumcheck, verify_approx_sumcheck
from poly import polynomial, term, monomial, get_multi_ext, get_ext


# =============================================================================
# Floating Point to Field Element Conversion
# =============================================================================

class FPFieldConverter:
    """
    Converts between IEEE 754 floating point and field elements.
    Uses scaled integer representation for arithmetic in the field.
    """
    
    # Scaling factor: we represent FP values as fixed-point in the field
    SCALE_BITS = 64  # Number of fractional bits
    SCALE_FACTOR = 2 ** SCALE_BITS
    
    @classmethod
    def fp_to_field(cls, fp: IEEE754Float) -> field.FQ:
        """
        Convert IEEE754Float to a field element using scaled representation.
        
        The value is represented as: sign * mantissa * 2^(exponent - bias - scale)
        """
        if fp.exponent == 0 and fp.mantissa == 0:
            return field.FQ.zero()
        
        # Get the actual floating point value
        val = fp.to_float()
        
        # Scale to fixed-point representation
        scaled = int(val * cls.SCALE_FACTOR)
        
        # Handle negative numbers in the field
        if scaled < 0:
            scaled = field.SNARK_SCALAR_FIELD + scaled
        
        return field.FQ(scaled)
    
    @classmethod
    def field_to_fp(cls, f: field.FQ) -> IEEE754Float:
        """
        Convert field element back to IEEE754Float.
        """
        val = int(f)
        
        # Handle negative numbers
        if val > field.SNARK_SCALAR_FIELD // 2:
            val = val - field.SNARK_SCALAR_FIELD
        
        # Unscale
        float_val = val / cls.SCALE_FACTOR
        
        return IEEE754Float.from_float(float_val)
    
    @classmethod
    def compute_field_epsilon(cls, fp_epsilon: float) -> field.FQ:
        """
        Convert floating point epsilon to field epsilon.
        """
        scaled_eps = int(fp_epsilon * cls.SCALE_FACTOR)
        return field.FQ(max(1, scaled_eps))


# =============================================================================
# Floating Point Multilinear Extension
# =============================================================================

def fp_values_to_mle(values: List[IEEE754Float], num_vars: int) -> polynomial:
    """
    Convert a list of floating point values to their multilinear extension.
    
    Args:
        values: List of IEEE754Float values (length must be 2^num_vars)
        num_vars: Number of variables in the MLE
    
    Returns:
        Multilinear extension polynomial
    """
    # Convert FP values to field elements
    field_values = [FPFieldConverter.fp_to_field(v) for v in values]
    
    # Pad to power of 2 if necessary
    target_len = 2 ** num_vars
    while len(field_values) < target_len:
        field_values.append(field.FQ.zero())
    
    # Create MLE
    return get_multi_ext(field_values, num_vars)


# =============================================================================
# Floating Point GKR Circuit Builder
# =============================================================================

class FPGKRCircuitBuilder:
    """
    Builds GKR circuits for floating point computations with proper
    error bound tracking for approximate sumcheck.
    """
    
    def __init__(self):
        self.layers: List[Dict[str, Any]] = []
        self.input_fps: List[IEEE754Float] = []
        self.wire_values: List[List[field.FQ]] = []
        self.epsilons: List[field.FQ] = []
    
    def set_inputs(self, values: List[float]):
        """Set input floating point values"""
        self.input_fps = [IEEE754Float.from_float(v) for v in values]
        self.wire_values = [[FPFieldConverter.fp_to_field(fp) for fp in self.input_fps]]
    
    def add_fp_add_layer(self, connections: List[Tuple[int, int]]):
        """
        Add a layer of floating point additions.
        
        Args:
            connections: List of (left_idx, right_idx) for each gate
        """
        layer_epsilon = field.FQ.zero()
        output_values = []
        
        prev_values = self.wire_values[-1]
        prev_fps = [FPFieldConverter.field_to_fp(v) for v in prev_values]
        
        for left_idx, right_idx in connections:
            a = prev_fps[left_idx]
            b = prev_fps[right_idx]
            result, eps = FPAddGate.compute(a, b)
            
            output_values.append(FPFieldConverter.fp_to_field(result))
            layer_epsilon = layer_epsilon + eps
        
        self.wire_values.append(output_values)
        self.epsilons.append(layer_epsilon)
        self.layers.append({
            'type': 'add',
            'connections': connections,
            'epsilon': layer_epsilon
        })
    
    def add_fp_mul_layer(self, connections: List[Tuple[int, int]]):
        """Add a layer of floating point multiplications."""
        layer_epsilon = field.FQ.zero()
        output_values = []
        
        prev_values = self.wire_values[-1]
        prev_fps = [FPFieldConverter.field_to_fp(v) for v in prev_values]
        
        for left_idx, right_idx in connections:
            a = prev_fps[left_idx]
            b = prev_fps[right_idx]
            result, eps = FPMulGate.compute(a, b)
            
            output_values.append(FPFieldConverter.fp_to_field(result))
            layer_epsilon = layer_epsilon + eps
        
        self.wire_values.append(output_values)
        self.epsilons.append(layer_epsilon)
        self.layers.append({
            'type': 'mul',
            'connections': connections,
            'epsilon': layer_epsilon
        })
    
    def add_mixed_layer(self, add_connections: List[Tuple[int, int]], 
                        mul_connections: List[Tuple[int, int]]):
        """Add a layer with both additions and multiplications."""
        layer_epsilon = field.FQ.zero()
        output_values = []
        
        prev_values = self.wire_values[-1]
        prev_fps = [FPFieldConverter.field_to_fp(v) for v in prev_values]
        
        # Process additions
        for left_idx, right_idx in add_connections:
            a = prev_fps[left_idx]
            b = prev_fps[right_idx]
            result, eps = FPAddGate.compute(a, b)
            output_values.append(FPFieldConverter.fp_to_field(result))
            layer_epsilon = layer_epsilon + eps
        
        # Process multiplications
        for left_idx, right_idx in mul_connections:
            a = prev_fps[left_idx]
            b = prev_fps[right_idx]
            result, eps = FPMulGate.compute(a, b)
            output_values.append(FPFieldConverter.fp_to_field(result))
            layer_epsilon = layer_epsilon + eps
        
        self.wire_values.append(output_values)
        self.epsilons.append(layer_epsilon)
        self.layers.append({
            'type': 'mixed',
            'add_connections': add_connections,
            'mul_connections': mul_connections,
            'epsilon': layer_epsilon
        })
    
    def get_total_epsilon(self) -> field.FQ:
        """Get total error bound across all layers"""
        return sum(self.epsilons, field.FQ.zero())
    
    def get_outputs(self) -> List[IEEE754Float]:
        """Get output floating point values"""
        return [FPFieldConverter.field_to_fp(v) for v in self.wire_values[-1]]
    
    def build_gkr_circuit(self) -> Circuit:
        """
        Build a GKR Circuit from the floating point circuit.
        """
        depth = len(self.layers) + 1
        circuit = Circuit(depth)
        
        # Build each layer
        for layer_idx, layer in enumerate(self.layers):
            num_outputs = len(self.wire_values[layer_idx + 1])
            k = max(1, int(math.ceil(math.log2(num_outputs)))) if num_outputs > 1 else 1
            
            # Define the W function for this layer
            layer_values = self.wire_values[layer_idx + 1]
            
            def make_w_func(values):
                def w_func(bits):
                    idx = 0
                    for b in bits:
                        idx = (idx << 1) | int(b)
                    if idx < len(values):
                        return values[idx]
                    return field.FQ.zero()
                return w_func
            
            circuit.layers[layer_idx].add_func(make_w_func(layer_values))
            
            # Define add and mult functions based on layer type
            if layer['type'] == 'add':
                circuit.layers[layer_idx].add = lambda arr: field.FQ.one()  # Simplified
                circuit.layers[layer_idx].mult = lambda arr: field.FQ.zero()
            elif layer['type'] == 'mul':
                circuit.layers[layer_idx].add = lambda arr: field.FQ.zero()
                circuit.layers[layer_idx].mult = lambda arr: field.FQ.one()
            else:  # mixed
                # Would need more sophisticated wiring function
                circuit.layers[layer_idx].add = lambda arr: field.FQ.one()
                circuit.layers[layer_idx].mult = lambda arr: field.FQ.one()
        
        return circuit


# =============================================================================
# Floating Point GKR Prover
# =============================================================================

@dataclass
class FPGKRProof:
    """
    Proof for floating point GKR computation.
    Includes both the standard GKR proof and FP-specific error bounds.
    """
    # GKR proof components
    sumcheck_proofs: List[List[List[field.FQ]]]
    sumcheck_r: List[List[field.FQ]]
    sumcheck_deltas: List[List[field.FQ]]  # Per-round error bounds
    
    # FP-specific components
    input_fps: List[IEEE754Float]
    output_fps: List[IEEE754Float]
    layer_epsilons: List[field.FQ]
    total_epsilon: field.FQ
    
    # Wire values for verification
    wire_values: List[List[field.FQ]]
    
    def to_dict(self) -> Dict:
        return {
            'sumcheck_proofs': [[[repr(c) for c in poly] for poly in layer] 
                               for layer in self.sumcheck_proofs],
            'sumcheck_r': [[repr(r) for r in layer] for layer in self.sumcheck_r],
            'sumcheck_deltas': [[repr(d) for d in layer] for layer in self.sumcheck_deltas],
            'input_fps': [{'s': fp.sign, 'e': fp.exponent, 'm': fp.mantissa} 
                         for fp in self.input_fps],
            'output_fps': [{'s': fp.sign, 'e': fp.exponent, 'm': fp.mantissa}
                          for fp in self.output_fps],
            'layer_epsilons': [repr(e) for e in self.layer_epsilons],
            'total_epsilon': repr(self.total_epsilon)
        }


def prove_fp_gkr(builder: FPGKRCircuitBuilder) -> FPGKRProof:
    """
    Generate a GKR proof for a floating point computation.
    
    Uses approximate sumcheck with error bounds derived from
    IEEE 754 rounding analysis.
    """
    sumcheck_proofs = []
    sumcheck_r = []
    sumcheck_deltas = []
    
    # For each layer transition, run approximate sumcheck
    for i in range(len(builder.layers)):
        prev_values = builder.wire_values[i]
        curr_values = builder.wire_values[i + 1]
        layer_epsilon = builder.epsilons[i]
        
        # Create MLE for current layer values
        num_vars = max(1, int(math.ceil(math.log2(len(curr_values))))) if curr_values else 1
        
        # Pad values to power of 2
        padded_values = list(curr_values)
        while len(padded_values) < 2 ** num_vars:
            padded_values.append(field.FQ.zero())
        
        # Create callable function for MLE evaluation
        # get_multi_ext expects a function that takes binary assignment and returns value
        def make_value_func(values):
            def value_func(bits):
                idx = 0
                for b in bits:
                    idx = (idx << 1) | int(b)
                if idx < len(values):
                    return values[idx]
                return field.FQ.zero()
            return value_func
        
        # Create the polynomial for sumcheck using get_ext (returns polynomial)
        mle = get_ext(make_value_func(padded_values), num_vars)
        
        # Run approximate sumcheck with layer epsilon as max_delta
        if num_vars > 0:
            approx_proof = prove_approx_sumcheck(
                mle, num_vars, 1,
                max_delta=layer_epsilon
            )
            sumcheck_proofs.append(approx_proof.polynomials)
            sumcheck_r.append(approx_proof.r)
            sumcheck_deltas.append(approx_proof.deltas)
        else:
            sumcheck_proofs.append([])
            sumcheck_r.append([])
            sumcheck_deltas.append([])
    
    return FPGKRProof(
        sumcheck_proofs=sumcheck_proofs,
        sumcheck_r=sumcheck_r,
        sumcheck_deltas=sumcheck_deltas,
        input_fps=builder.input_fps,
        output_fps=builder.get_outputs(),
        layer_epsilons=builder.epsilons,
        total_epsilon=builder.get_total_epsilon(),
        wire_values=builder.wire_values
    )


# =============================================================================
# Floating Point GKR Verifier  
# =============================================================================

def verify_fp_gkr(proof: FPGKRProof, expected_outputs: Optional[List[float]] = None,
                  ulp_tolerance: int = 1) -> Tuple[bool, Dict[str, Any]]:
    """
    Verify a floating point GKR proof.
    
    Args:
        proof: The FP GKR proof
        expected_outputs: Optional expected output values for comparison
        ulp_tolerance: Maximum allowed ULP error
    
    Returns:
        (is_valid, verification_info)
    """
    verification_info = {
        'sumcheck_valid': True,
        'output_errors_ulp': [],
        'total_accumulated_error': field.FQ.zero(),
        'max_ulp_error': 0.0
    }
    
    total_error = field.FQ.zero()
    
    # Verify each layer's sumcheck
    for i in range(len(proof.sumcheck_proofs)):
        if not proof.sumcheck_proofs[i]:
            continue
            
        # Reconstruct the claim for this layer
        curr_values = proof.wire_values[i + 1]
        claim = sum(curr_values, field.FQ.zero())
        
        # Create ApproxSumcheckProof
        approx_proof = ApproxSumcheckProof(
            proof.sumcheck_proofs[i],
            proof.sumcheck_deltas[i],
            proof.sumcheck_r[i]
        )
        
        num_vars = len(proof.sumcheck_r[i])
        if num_vars > 0:
            valid, layer_error = verify_approx_sumcheck(
                claim, approx_proof, num_vars,
                base_delta=proof.layer_epsilons[i]
            )
            
            if not valid:
                verification_info['sumcheck_valid'] = False
                return False, verification_info
            
            total_error = total_error + layer_error
    
    verification_info['total_accumulated_error'] = total_error
    
    # Check output values if expected values provided
    if expected_outputs:
        for i, (computed_fp, expected) in enumerate(zip(proof.output_fps, expected_outputs)):
            computed = computed_fp.to_float()
            
            if expected != 0:
                expected_fp = IEEE754Float.from_float(expected)
                ulp = compute_ulp(expected_fp)
                error_ulp = abs(computed - expected) / ulp if ulp > 0 else float('inf')
            else:
                error_ulp = abs(computed) * (2 ** IEEE754Float.MANTISSA_BITS)
            
            verification_info['output_errors_ulp'].append(error_ulp)
            verification_info['max_ulp_error'] = max(
                verification_info['max_ulp_error'], 
                error_ulp
            )
        
        if verification_info['max_ulp_error'] > ulp_tolerance:
            return False, verification_info
    
    # Check total error is within bounds
    if int(total_error) > int(proof.total_epsilon):
        return False, verification_info
    
    return True, verification_info


# =============================================================================
# High-Level API
# =============================================================================

def fp_prove_computation(operation: str, inputs: List[float]) -> FPGKRProof:
    """
    High-level API to prove a floating point computation.
    
    Args:
        operation: 'dot_product', 'matmul', 'sum', 'product'
        inputs: Input values
    
    Returns:
        FPGKRProof
    """
    builder = FPGKRCircuitBuilder()
    builder.set_inputs(inputs)
    
    if operation == 'sum':
        # Tree reduction sum
        n = len(inputs)
        current_size = n
        while current_size > 1:
            connections = [(2*i, 2*i+1) for i in range(current_size // 2)]
            if current_size % 2 == 1:
                connections.append((current_size - 1, current_size - 1))
            builder.add_fp_add_layer(connections)
            current_size = (current_size + 1) // 2
    
    elif operation == 'product':
        # Tree reduction product
        n = len(inputs)
        current_size = n
        while current_size > 1:
            connections = [(2*i, 2*i+1) for i in range(current_size // 2)]
            if current_size % 2 == 1:
                connections.append((current_size - 1, current_size - 1))
            builder.add_fp_mul_layer(connections)
            current_size = (current_size + 1) // 2
    
    elif operation == 'dot_product':
        # Assumes inputs = [a0, a1, ..., an-1, b0, b1, ..., bn-1]
        n = len(inputs) // 2
        
        # Layer 1: Element-wise multiplication
        mul_connections = [(i, n + i) for i in range(n)]
        builder.add_fp_mul_layer(mul_connections)
        
        # Layers 2+: Tree reduction sum
        current_size = n
        while current_size > 1:
            connections = [(2*i, 2*i+1) for i in range(current_size // 2)]
            if current_size % 2 == 1:
                connections.append((current_size - 1, current_size - 1))
            builder.add_fp_add_layer(connections)
            current_size = (current_size + 1) // 2
    
    return prove_fp_gkr(builder)


def fp_verify_computation(proof: FPGKRProof, expected: Optional[float] = None) -> bool:
    """
    High-level API to verify a floating point computation proof.
    """
    expected_outputs = [expected] if expected is not None else None
    valid, _ = verify_fp_gkr(proof, expected_outputs)
    return valid


# =============================================================================
# Tests
# =============================================================================

def test_fp_sum():
    """Test floating point sum with GKR"""
    inputs = [1.1, 2.2, 3.3, 4.4]
    expected = sum(inputs)
    
    print("Testing FP Sum:")
    print(f"  Inputs: {inputs}")
    print(f"  Expected: {expected}")
    
    proof = fp_prove_computation('sum', inputs)
    print(f"  Computed: {proof.output_fps[0].to_float()}")
    print(f"  Total epsilon: {proof.total_epsilon}")
    
    valid, info = verify_fp_gkr(proof, [expected])
    print(f"  Valid: {valid}")
    print(f"  Max ULP error: {info['max_ulp_error']:.2f}")


def test_fp_dot_product():
    """Test floating point dot product with GKR"""
    a = [1.0, 2.0, 3.0, 4.0]
    b = [0.5, 1.5, 2.5, 3.5]
    expected = sum(x * y for x, y in zip(a, b))
    
    print("\nTesting FP Dot Product:")
    print(f"  a = {a}")
    print(f"  b = {b}")
    print(f"  Expected: {expected}")
    
    proof = fp_prove_computation('dot_product', a + b)
    print(f"  Computed: {proof.output_fps[0].to_float()}")
    print(f"  Total epsilon: {proof.total_epsilon}")
    
    valid, info = verify_fp_gkr(proof, [expected])
    print(f"  Valid: {valid}")
    print(f"  Max ULP error: {info['max_ulp_error']:.2f}")


def test_fp_product():
    """Test floating point product with GKR"""
    inputs = [1.1, 2.2, 3.3, 4.4]
    expected = 1.0
    for x in inputs:
        expected *= x
    
    print("\nTesting FP Product:")
    print(f"  Inputs: {inputs}")
    print(f"  Expected: {expected}")
    
    proof = fp_prove_computation('product', inputs)
    print(f"  Computed: {proof.output_fps[0].to_float()}")
    print(f"  Total epsilon: {proof.total_epsilon}")
    
    valid, info = verify_fp_gkr(proof, [expected])
    print(f"  Valid: {valid}")
    print(f"  Max ULP error: {info['max_ulp_error']:.2f}")


if __name__ == "__main__":
    test_fp_sum()
    test_fp_dot_product()
    test_fp_product()
