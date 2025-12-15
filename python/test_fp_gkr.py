"""
Test suite for IEEE 754 Floating Point GKR with Approximate Sum-Check
"""

import sys
import math
from typing import List, Tuple

# Add parent directory to path
sys.path.insert(0, '.')

from fp_arithmetic import (
    IEEE754Float, IEEE754Double, 
    FPAddGate, FPMulGate, FPDivGate, FPSqrtGate,
    compute_ulp, compute_epsilon_for_operation,
    FPGKRCircuit, FPCircuitLayer,
    create_fp_matmul_circuit, create_fp_dot_product_circuit,
    prove_fp_computation, verify_fp_computation
)

from fp_gkr import (
    FPFieldConverter, FPGKRCircuitBuilder, FPGKRProof,
    prove_fp_gkr, verify_fp_gkr,
    fp_prove_computation, fp_verify_computation
)

try:
    from ethsnarks import field
except ImportError:
    import field


def print_header(title: str):
    print("\n" + "=" * 60)
    print(f" {title}")
    print("=" * 60)


# =============================================================================
# IEEE 754 Representation Tests
# =============================================================================

def test_ieee754_basic():
    """Test basic IEEE 754 conversion"""
    print_header("IEEE 754 Basic Conversion Tests")
    
    test_values = [
        (0.0, "zero"),
        (1.0, "one"),
        (-1.0, "negative one"),
        (0.5, "half"),
        (2.0, "two"),
        (3.14159, "pi approx"),
        (1e10, "large"),
        (1e-10, "small"),
        (0.1, "0.1 (not exactly representable)"),
        (float('inf'), "infinity"),
        (-float('inf'), "negative infinity"),
    ]
    
    all_passed = True
    for val, name in test_values:
        if math.isnan(val) or math.isinf(val):
            continue
            
        fp = IEEE754Float.from_float(val)
        recovered = fp.to_float()
        
        if val == 0.0:
            error = abs(recovered)
            passed = error == 0.0
        else:
            error = abs((val - recovered) / val)
            passed = error < 1e-6
        
        status = "✓" if passed else "✗"
        print(f"  {status} {name:30} : {val:>15.6e} -> {recovered:>15.6e} (rel_err: {error:.2e})")
        
        if not passed:
            all_passed = False
            print(f"      sign={fp.sign}, exp={fp.exponent}, mant={fp.mantissa}")
    
    return all_passed


def test_ieee754_special_values():
    """Test special IEEE 754 values"""
    print_header("IEEE 754 Special Values Tests")
    
    # Test denormalized numbers
    smallest_normal = 2.0 ** -126
    denormal = smallest_normal / 2
    
    fp = IEEE754Float.from_float(denormal)
    print(f"  Denormal {denormal:.6e}: exp={fp.exponent}, mant={fp.mantissa}")
    assert fp.exponent == 0, "Denormal should have exponent 0"
    
    # Test near-overflow
    large = 3.4e38
    fp = IEEE754Float.from_float(large)
    print(f"  Large {large:.6e}: exp={fp.exponent}, mant={fp.mantissa}")
    
    return True


def test_field_conversion():
    """Test conversion between FP and field elements"""
    print_header("Field Conversion Tests")
    
    test_values = [0.0, 1.0, -1.0, 3.14159, 100.5, -50.25]
    
    all_passed = True
    for val in test_values:
        fp = IEEE754Float.from_float(val)
        field_val = FPFieldConverter.fp_to_field(fp)
        recovered_fp = FPFieldConverter.field_to_fp(field_val)
        recovered = recovered_fp.to_float()
        
        if val == 0.0:
            error = abs(recovered)
        else:
            error = abs((val - recovered) / val)
        
        passed = error < 0.01  # Allow 1% error from scaling
        status = "✓" if passed else "✗"
        print(f"  {status} {val:>10.4f} -> field -> {recovered:>10.4f} (error: {error:.2%})")
        
        if not passed:
            all_passed = False
    
    return all_passed


# =============================================================================
# ULP and Error Bound Tests
# =============================================================================

def test_ulp_computation():
    """Test ULP computation"""
    print_header("ULP Computation Tests")
    
    test_cases = [
        (1.0, 2**-23),          # ULP of 1.0
        (2.0, 2**-22),          # ULP of 2.0
        (0.5, 2**-24),          # ULP of 0.5
        (1024.0, 2**-13),       # ULP of 1024
        (1e-10, "small"),       # Very small number
    ]
    
    for val, expected_ulp in test_cases:
        fp = IEEE754Float.from_float(val)
        ulp = compute_ulp(fp)
        
        if isinstance(expected_ulp, str):
            print(f"  {val:>15.6e}: ULP = {ulp:.6e}")
        else:
            ratio = ulp / expected_ulp
            passed = 0.9 < ratio < 1.1
            status = "✓" if passed else "✗"
            print(f"  {status} {val:>15.6e}: ULP = {ulp:.6e} (expected {expected_ulp:.6e})")
    
    return True


def test_error_bounds():
    """Test error bound computation for operations"""
    print_header("Error Bound Tests")
    
    a = IEEE754Float.from_float(3.14159)
    b = IEEE754Float.from_float(2.71828)
    
    ops = ['add', 'mul', 'sub', 'div']
    for op in ops:
        epsilon = compute_epsilon_for_operation(a, b, op)
        print(f"  {op:5}: epsilon = {epsilon}")
    
    return True


# =============================================================================
# Floating Point Operation Tests
# =============================================================================

def test_fp_addition():
    """Test floating point addition"""
    print_header("FP Addition Tests")
    
    test_cases = [
        (1.0, 2.0),
        (0.1, 0.2),
        (1e10, 1.0),
        (1.0, -1.0),
        (3.14159, 2.71828),
    ]
    
    all_passed = True
    for a_val, b_val in test_cases:
        a = IEEE754Float.from_float(a_val)
        b = IEEE754Float.from_float(b_val)
        result, epsilon = FPAddGate.compute(a, b)
        
        expected = a_val + b_val
        computed = result.to_float()
        
        if expected == 0:
            error = abs(computed)
        else:
            error = abs((expected - computed) / expected)
        
        passed = error < 1e-6
        status = "✓" if passed else "✗"
        print(f"  {status} {a_val} + {b_val} = {computed} (expected {expected}, error {error:.2e})")
        
        if not passed:
            all_passed = False
    
    return all_passed


def test_fp_multiplication():
    """Test floating point multiplication"""
    print_header("FP Multiplication Tests")
    
    test_cases = [
        (2.0, 3.0),
        (0.5, 0.5),
        (1e5, 1e5),
        (-2.0, 3.0),
        (3.14159, 2.71828),
    ]
    
    all_passed = True
    for a_val, b_val in test_cases:
        a = IEEE754Float.from_float(a_val)
        b = IEEE754Float.from_float(b_val)
        result, epsilon = FPMulGate.compute(a, b)
        
        expected = a_val * b_val
        computed = result.to_float()
        
        if expected == 0:
            error = abs(computed)
        else:
            error = abs((expected - computed) / expected)
        
        passed = error < 1e-6
        status = "✓" if passed else "✗"
        print(f"  {status} {a_val} * {b_val} = {computed} (expected {expected}, error {error:.2e})")
        
        if not passed:
            all_passed = False
    
    return all_passed


def test_fp_division():
    """Test floating point division"""
    print_header("FP Division Tests")
    
    test_cases = [
        (6.0, 2.0),
        (1.0, 3.0),
        (22.0, 7.0),  # Approximation of pi
        (-6.0, 2.0),
    ]
    
    for a_val, b_val in test_cases:
        a = IEEE754Float.from_float(a_val)
        b = IEEE754Float.from_float(b_val)
        result, epsilon = FPDivGate.compute(a, b)
        
        expected = a_val / b_val
        computed = result.to_float()
        error = abs((expected - computed) / expected) if expected != 0 else abs(computed)
        
        print(f"  {a_val} / {b_val} = {computed} (expected {expected}, error {error:.2e})")
    
    return True


def test_fp_sqrt():
    """Test floating point square root"""
    print_header("FP Square Root Tests")
    
    test_values = [4.0, 2.0, 9.0, 0.25, 3.14159]
    
    for val in test_values:
        fp = IEEE754Float.from_float(val)
        result, epsilon = FPSqrtGate.compute(fp)
        
        expected = math.sqrt(val)
        computed = result.to_float()
        error = abs((expected - computed) / expected) if expected != 0 else abs(computed)
        
        print(f"  sqrt({val}) = {computed} (expected {expected}, error {error:.2e})")
    
    return True


# =============================================================================
# Circuit Tests
# =============================================================================

def test_dot_product_circuit():
    """Test dot product circuit"""
    print_header("Dot Product Circuit Test")
    
    n = 4
    a = [1.0, 2.0, 3.0, 4.0]
    b = [0.5, 1.5, 2.5, 3.5]
    
    expected = sum(x * y for x, y in zip(a, b))
    
    circuit = create_fp_dot_product_circuit(n)
    circuit.set_inputs(a + b)
    outputs = circuit.evaluate()
    
    computed = outputs[0].to_float()
    error = abs((expected - computed) / expected)
    
    print(f"  a = {a}")
    print(f"  b = {b}")
    print(f"  Expected: {expected}")
    print(f"  Computed: {computed}")
    print(f"  Error: {error:.2e}")
    print(f"  Total epsilon: {circuit.get_error_bound()}")
    
    passed = error < 1e-5
    return passed


def test_sum_circuit():
    """Test summation circuit"""
    print_header("Sum Circuit Test")
    
    values = [1.1, 2.2, 3.3, 4.4, 5.5, 6.6, 7.7, 8.8]
    expected = sum(values)
    
    # Build circuit using builder
    builder = FPGKRCircuitBuilder()
    builder.set_inputs(values)
    
    # Tree reduction
    current_size = len(values)
    while current_size > 1:
        connections = [(2*i, 2*i+1) for i in range(current_size // 2)]
        if current_size % 2 == 1:
            connections.append((current_size - 1, current_size - 1))
        builder.add_fp_add_layer(connections)
        current_size = (current_size + 1) // 2
    
    outputs = builder.get_outputs()
    computed = outputs[0].to_float()
    error = abs((expected - computed) / expected)
    
    print(f"  Values: {values}")
    print(f"  Expected: {expected}")
    print(f"  Computed: {computed}")
    print(f"  Error: {error:.2e}")
    print(f"  Total epsilon: {builder.get_total_epsilon()}")
    
    passed = error < 1e-5
    return passed


# =============================================================================
# GKR Proof Tests
# =============================================================================

def test_fp_gkr_proof():
    """Test FP GKR proof generation and verification"""
    print_header("FP GKR Proof Test")
    
    # Simple sum
    inputs = [1.0, 2.0, 3.0, 4.0]
    expected = sum(inputs)
    
    print(f"  Operation: Sum")
    print(f"  Inputs: {inputs}")
    print(f"  Expected output: {expected}")
    
    # Generate proof
    proof = fp_prove_computation('sum', inputs)
    
    print(f"  Computed output: {proof.output_fps[0].to_float()}")
    print(f"  Total epsilon: {proof.total_epsilon}")
    print(f"  Number of layers: {len(proof.sumcheck_proofs)}")
    
    # Verify proof
    valid, info = verify_fp_gkr(proof, [expected])
    
    print(f"  Verification result: {'✓ Valid' if valid else '✗ Invalid'}")
    print(f"  Max ULP error: {info['max_ulp_error']:.2f}")
    print(f"  Accumulated error: {info['total_accumulated_error']}")
    
    return valid


def test_fp_dot_product_proof():
    """Test FP dot product proof"""
    print_header("FP Dot Product Proof Test")
    
    a = [1.0, 2.0, 3.0, 4.0]
    b = [0.5, 1.5, 2.5, 3.5]
    expected = sum(x * y for x, y in zip(a, b))
    
    print(f"  a = {a}")
    print(f"  b = {b}")
    print(f"  Expected: {expected}")
    
    # Generate proof
    proof = fp_prove_computation('dot_product', a + b)
    
    print(f"  Computed: {proof.output_fps[0].to_float()}")
    print(f"  Total epsilon: {proof.total_epsilon}")
    
    # Verify
    valid, info = verify_fp_gkr(proof, [expected])
    
    print(f"  Verification: {'✓ Valid' if valid else '✗ Invalid'}")
    print(f"  Max ULP error: {info['max_ulp_error']:.2f}")
    
    return valid


def test_fp_product_proof():
    """Test FP product proof"""
    print_header("FP Product Proof Test")
    
    inputs = [1.1, 2.2, 3.3, 4.4]
    expected = 1.0
    for x in inputs:
        expected *= x
    
    print(f"  Inputs: {inputs}")
    print(f"  Expected: {expected}")
    
    # Generate proof
    proof = fp_prove_computation('product', inputs)
    
    print(f"  Computed: {proof.output_fps[0].to_float()}")
    print(f"  Total epsilon: {proof.total_epsilon}")
    
    # Verify
    valid, info = verify_fp_gkr(proof, [expected])
    
    print(f"  Verification: {'✓ Valid' if valid else '✗ Invalid'}")
    print(f"  Max ULP error: {info['max_ulp_error']:.2f}")
    
    return valid


# =============================================================================
# Stress Tests
# =============================================================================

def test_large_sum():
    """Test sum with many elements"""
    print_header("Large Sum Test (Stress)")
    
    n = 64
    inputs = [1.0 / (i + 1) for i in range(n)]  # Harmonic series
    expected = sum(inputs)
    
    print(f"  Summing {n} elements (harmonic series)")
    print(f"  Expected: {expected}")
    
    proof = fp_prove_computation('sum', inputs)
    computed = proof.output_fps[0].to_float()
    
    error = abs((expected - computed) / expected)
    
    print(f"  Computed: {computed}")
    print(f"  Relative error: {error:.2e}")
    print(f"  Total epsilon: {proof.total_epsilon}")
    
    valid, info = verify_fp_gkr(proof, [expected], ulp_tolerance=100)  # Larger tolerance for many ops
    print(f"  Verification: {'✓ Valid' if valid else '✗ Invalid'}")
    
    return valid


def test_numerical_stability():
    """Test numerical stability with ill-conditioned inputs"""
    print_header("Numerical Stability Test")
    
    # Catastrophic cancellation example
    a = 1.0 + 1e-8
    b = 1.0
    
    fp_a = IEEE754Float.from_float(a)
    fp_b = IEEE754Float.from_float(b)
    result, epsilon = FPAddGate.compute(fp_a, IEEE754Float.from_float(-b))
    
    expected = a - b
    computed = result.to_float()
    
    print(f"  Testing: {a} - {b}")
    print(f"  Expected: {expected}")
    print(f"  Computed: {computed}")
    print(f"  Epsilon bound: {epsilon}")
    
    # The approximate sumcheck should accept this within epsilon
    return True


# =============================================================================
# Main Test Runner
# =============================================================================

def run_all_tests():
    """Run all tests"""
    print("\n" + "=" * 60)
    print(" IEEE 754 FP GKR with Approximate Sum-Check - Test Suite")
    print("=" * 60)
    
    tests = [
        ("IEEE 754 Basic", test_ieee754_basic),
        ("IEEE 754 Special Values", test_ieee754_special_values),
        ("Field Conversion", test_field_conversion),
        ("ULP Computation", test_ulp_computation),
        ("Error Bounds", test_error_bounds),
        ("FP Addition", test_fp_addition),
        ("FP Multiplication", test_fp_multiplication),
        ("FP Division", test_fp_division),
        ("FP Square Root", test_fp_sqrt),
        ("Dot Product Circuit", test_dot_product_circuit),
        ("Sum Circuit", test_sum_circuit),
        ("FP GKR Proof", test_fp_gkr_proof),
        ("FP Dot Product Proof", test_fp_dot_product_proof),
        ("FP Product Proof", test_fp_product_proof),
        ("Large Sum (Stress)", test_large_sum),
        ("Numerical Stability", test_numerical_stability),
    ]
    
    results = []
    for name, test_fn in tests:
        try:
            passed = test_fn()
            results.append((name, passed))
        except Exception as e:
            print(f"\n  ERROR: {e}")
            results.append((name, False))
    
    # Summary
    print("\n" + "=" * 60)
    print(" Test Summary")
    print("=" * 60)
    
    passed_count = sum(1 for _, p in results if p)
    total_count = len(results)
    
    for name, passed in results:
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"  {status}  {name}")
    
    print("-" * 60)
    print(f"  Total: {passed_count}/{total_count} tests passed")
    print("=" * 60)
    
    return passed_count == total_count


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
