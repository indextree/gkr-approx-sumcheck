from poly import *
from util import *
from typing import Callable, Tuple, List, Optional
try:
    from ethsnarks import mimc
except ImportError:
    import mimc

# =============================================================================
# Approximate Sum-Check Protocol
# Based on "Sum-Check Protocol for Approximate Computations" (2025)
# 
# Key difference from standard sumcheck:
# - Standard: g_i(0) + g_i(1) = c_i (exact equality)
# - Approximate: |g_i(0) + g_i(1) - c_i| <= epsilon_i (within error tolerance)
#
# The prover sends error bounds (delta_i) along with each round's polynomial.
# Errors accumulate across rounds according to the paper's analysis.
# =============================================================================

class ApproxSumcheckProof:
    """
    Approximate sumcheck proof structure containing:
    - polynomials: List of univariate polynomials (coefficients) for each round
    - deltas: Error bounds for each round (delta_i)
    - r: Random challenges for each round
    """
    def __init__(self, polynomials: List[List[field.FQ]], 
                 deltas: List[field.FQ], 
                 r: List[field.FQ]):
        self.polynomials = polynomials
        self.deltas = deltas  # Error bounds per round
        self.r = r

    def to_dict(self):
        return {
            'polynomials': [[repr(c) for c in poly] for poly in self.polynomials],
            'deltas': [repr(d) for d in self.deltas],
            'r': [repr(ri) for ri in self.r]
        }


def prove_sumcheck(g: polynomial, v: int, start: int, 
                   epsilon: field.FQ = field.FQ.zero()) -> Tuple[List[List[field.FQ]], List[field.FQ]]:
    """
    Standard sumcheck prover (backward compatible).
    For approximate sumcheck, use prove_approx_sumcheck instead.
    """
    proof = []
    r = []
    # first round
    # g1(X1)=∑(x2,⋯,xv)∈{0,1}^v g(X_1,x_2,⋯,x_v)    
    g_1 = polynomial([])
    assignments = generate_binary(v - 1)
    for assignment in assignments:
        g_1_sub = polynomial(g.terms[:], g.constant)
        for i, x_i in enumerate(assignment):
            idx = i + 1 + start
            g_1_sub = g_1_sub.eval_i(x_i, idx)
        g_1 += g_1_sub
    proof.append(g_1.get_all_coefficients())

    r_1 = field.FQ(mimc.mimc_hash(list(map(lambda x : int(x), g_1.get_all_coefficients()))))
    r.append(r_1)

    # 1 < j < v round
    for j in range(1, v - 1):
        g_j = polynomial(g.terms[:], g.constant)
        assignments = generate_binary(v - j - 1)
        for i, r_i in enumerate(r):
            idx = i + start
            g_j = g_j.eval_i(r_i, idx)
        
        res_g_j = polynomial([])
        for assignment in assignments:
            g_j_sub = polynomial(g_j.terms[:], g_j.constant)
            for k, x_i in enumerate(assignment):
                idx = j + k + start + 1
                g_j_sub = g_j_sub.eval_i(x_i, idx)
            res_g_j += g_j_sub
        proof.append(res_g_j.get_all_coefficients())

        r_n = field.FQ(mimc.mimc_hash(list(map(lambda x : int(x), proof[len(proof) - 1]))))
        r.append(r_n)

    g_v = polynomial(g.terms[:], g.constant)
    for i, r_i in enumerate(r):
        idx = i + start
        g_v = g_v.eval_i(r_i, idx)
    proof.append(g_v.get_all_coefficients())

    r_v = field.FQ(mimc.mimc_hash(list(map(lambda x : int(x), proof[len(proof) - 1]))))
    r.append(r_v)

    return proof, r


def prove_approx_sumcheck(g: polynomial, v: int, start: int,
                          approx_values: Optional[List[field.FQ]] = None,
                          max_delta: field.FQ = field.FQ.zero()) -> ApproxSumcheckProof:
    """
    Approximate Sum-Check Prover
    
    Based on the paper "Sum-Check Protocol for Approximate Computations":
    - The prover can use approximate polynomial evaluations
    - For each round, prover sends (g_i, delta_i) where delta_i is the error bound
    - The sum g_i(0) + g_i(1) may differ from the expected claim by at most delta_i
    
    Args:
        g: The multivariate polynomial to sum over
        v: Number of variables
        start: Starting index for variable numbering
        approx_values: Optional pre-computed approximate values (for testing)
        max_delta: Maximum allowed error per round
    
    Returns:
        ApproxSumcheckProof containing polynomials, error bounds, and challenges
    """
    proof = []
    deltas = []
    r = []
    
    # First round: g_1(X_1) = sum_{x_2,...,x_v in {0,1}^{v-1}} g(X_1, x_2, ..., x_v)
    g_1 = polynomial([])
    assignments = generate_binary(v - 1)
    for assignment in assignments:
        g_1_sub = polynomial(g.terms[:], g.constant)
        for i, x_i in enumerate(assignment):
            idx = i + 1 + start
            g_1_sub = g_1_sub.eval_i(x_i, idx)
        g_1 += g_1_sub
    
    # In approximate sumcheck, we may introduce error here
    # For now, delta_1 = 0 for exact computation, or max_delta for approximate
    proof.append(g_1.get_all_coefficients())
    deltas.append(max_delta)
    
    # Generate challenge using Fiat-Shamir (hash of polynomial + delta)
    hash_input = list(map(lambda x: int(x), g_1.get_all_coefficients()))
    hash_input.append(int(max_delta))
    r_1 = field.FQ(mimc.mimc_hash(hash_input))
    r.append(r_1)
    
    # Rounds j = 2, ..., v-1
    for j in range(1, v - 1):
        g_j = polynomial(g.terms[:], g.constant)
        assignments = generate_binary(v - j - 1)
        
        for i, r_i in enumerate(r):
            idx = i + start
            g_j = g_j.eval_i(r_i, idx)
        
        res_g_j = polynomial([])
        for assignment in assignments:
            g_j_sub = polynomial(g_j.terms[:], g_j.constant)
            for k, x_i in enumerate(assignment):
                idx = j + k + start + 1
                g_j_sub = g_j_sub.eval_i(x_i, idx)
            res_g_j += g_j_sub
        
        proof.append(res_g_j.get_all_coefficients())
        deltas.append(max_delta)
        
        hash_input = list(map(lambda x: int(x), proof[-1]))
        hash_input.append(int(max_delta))
        r_n = field.FQ(mimc.mimc_hash(hash_input))
        r.append(r_n)
    
    # Final round
    g_v = polynomial(g.terms[:], g.constant)
    for i, r_i in enumerate(r):
        idx = i + start
        g_v = g_v.eval_i(r_i, idx)
    proof.append(g_v.get_all_coefficients())
    deltas.append(max_delta)
    
    hash_input = list(map(lambda x: int(x), proof[-1]))
    hash_input.append(int(max_delta))
    r_v = field.FQ(mimc.mimc_hash(hash_input))
    r.append(r_v)
    
    return ApproxSumcheckProof(proof, deltas, r)


def verify_sumcheck(claim: field.FQ, proof: list[list[field.FQ]], r, v: int) -> bool:
    """
    Standard sumcheck verifier (backward compatible).
    For approximate sumcheck, use verify_approx_sumcheck instead.
    """
    bn = len(proof)
    if(v == 1 and (eval_univariate(proof[0], field.FQ.zero()) + eval_univariate(proof[0], field.FQ.one())) == claim):
        return True
    expected = claim
    for i in range(bn):
        q_zero = eval_univariate(proof[i], field.FQ.zero())
        q_one = eval_univariate(proof[i], field.FQ.one())

        if q_zero + q_one != expected:
            return False
        if field.FQ(mimc.mimc_hash(list(map(lambda x : int(x), proof[i])))) != r[i]:
            return False
        expected = eval_univariate(proof[i], r[i])

    return True


def abs_field(x: field.FQ) -> field.FQ:
    """
    Compute absolute value in the field.
    For a prime field F_p, we consider x "negative" if x > p/2.
    |x| = min(x, p - x)
    """
    p = field.SNARK_SCALAR_FIELD
    x_int = int(x)
    if x_int > p // 2:
        return field.FQ(p - x_int)
    return x


def verify_approx_sumcheck(claim: field.FQ, 
                           approx_proof: ApproxSumcheckProof, 
                           v: int,
                           total_epsilon: Optional[field.FQ] = None) -> Tuple[bool, field.FQ]:
    """
    Approximate Sum-Check Verifier
    
    Based on "Sum-Check Protocol for Approximate Computations":
    - Instead of checking g_i(0) + g_i(1) == expected, we check:
      |g_i(0) + g_i(1) - expected| <= epsilon_i
    - The total accumulated error must be bounded
    
    Args:
        claim: The claimed sum value (may be approximate)
        approx_proof: ApproxSumcheckProof containing polynomials, deltas, and r
        v: Number of variables
        total_epsilon: Maximum total allowed error (if None, computed from deltas)
    
    Returns:
        (is_valid, accumulated_error): Whether proof is valid and the total error
    """
    proof = approx_proof.polynomials
    deltas = approx_proof.deltas
    r = approx_proof.r
    bn = len(proof)
    
    # Compute total allowed error from per-round deltas
    # According to the paper, error accumulates: epsilon_total = sum of delta_i
    if total_epsilon is None:
        total_epsilon = sum(deltas, field.FQ.zero())
    
    accumulated_error = field.FQ.zero()
    expected = claim
    
    # Special case for v == 1
    if v == 1:
        sum_val = eval_univariate(proof[0], field.FQ.zero()) + eval_univariate(proof[0], field.FQ.one())
        error = abs_field(sum_val - claim)
        if int(error) <= int(total_epsilon):
            return True, error
        return False, error
    
    for i in range(bn):
        q_zero = eval_univariate(proof[i], field.FQ.zero())
        q_one = eval_univariate(proof[i], field.FQ.one())
        
        # Approximate check: |g_i(0) + g_i(1) - expected| <= delta_i
        actual_sum = q_zero + q_one
        round_error = abs_field(actual_sum - expected)
        
        # Check if round error is within allowed delta for this round
        if int(round_error) > int(deltas[i]):
            return False, accumulated_error + round_error
        
        accumulated_error = accumulated_error + round_error
        
        # Verify the random challenge was computed correctly (Fiat-Shamir)
        hash_input = list(map(lambda x: int(x), proof[i]))
        hash_input.append(int(deltas[i]))
        expected_r = field.FQ(mimc.mimc_hash(hash_input))
        if expected_r != r[i]:
            return False, accumulated_error
        
        # Update expected value for next round
        expected = eval_univariate(proof[i], r[i])
    
    # Check total accumulated error is within bounds
    if int(accumulated_error) > int(total_epsilon):
        return False, accumulated_error
    
    return True, accumulated_error


def verify_approx_sumcheck_simple(claim: field.FQ,
                                  proof: List[List[field.FQ]],
                                  r: List[field.FQ],
                                  v: int,
                                  epsilon: field.FQ = field.FQ.zero()) -> bool:
    """
    Simplified approximate sumcheck verifier (for backward compatibility).
    
    Uses a single epsilon tolerance for all rounds.
    """
    bn = len(proof)
    
    if v == 1:
        sum_val = eval_univariate(proof[0], field.FQ.zero()) + eval_univariate(proof[0], field.FQ.one())
        error = abs_field(sum_val - claim)
        return int(error) <= int(epsilon)
    
    expected = claim
    for i in range(bn):
        q_zero = eval_univariate(proof[i], field.FQ.zero())
        q_one = eval_univariate(proof[i], field.FQ.one())
        
        # Approximate check instead of exact equality
        actual_sum = q_zero + q_one
        error = abs_field(actual_sum - expected)
        
        if int(error) > int(epsilon):
            return False
        
        if field.FQ(mimc.mimc_hash(list(map(lambda x: int(x), proof[i])))) != r[i]:
            return False
        
        expected = eval_univariate(proof[i], r[i])
    
    return True
