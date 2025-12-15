import math
import time
from poly import *
from sumcheck import *

# =============================================================================
# GKR Protocol with Approximate Sumcheck Support
# Based on "Sum-Check Protocol for Approximate Computations" (2025)
# =============================================================================

class Node:
  def __init__(self, binary_index: list[int], value, left=None, right=None):
    self.binary_index = binary_index
    self.value = value
    self.left = left
    self.right = right

class Layer:
    def __init__(self) -> None:
        self.nodes = []

    def def_mult(self, mult):
        self.mult = mult

    def def_add(self, add):
        self.add = add

    def get_node(self, index) -> Node:
        return self.nodes[index]

    def add_node(self, index, node) -> None:
        self.nodes.insert(index, node)

    def add_func(self, func):
        self.func = func

    def len(self):
        return len(self.nodes)

class Circuit:
    def __init__(self, depth):
        layers = []
        for _ in range(depth):
            layers.append(Layer())
        self.layers : list[Layer] = layers # type: ignore
    
    def get_node(self, layer, index):
        return self.layers[layer].get_node(index)

    def add_node(self, layer, index, binary_index, value, left=None, right=None):
        self.layers[layer].add_node(index, Node(binary_index, value, left, right))

    def depth(self):
        return len(self.layers)

    def layer_length(self, layer):
        return self.layers[layer].len()
    
    def k_i(self, layer):
        return int(math.log2(self.layer_length(layer)))

    def add_i(self, i):
        return self.layers[i].add
    
    def mult_i(self, i):
        return self.layers[i].mult
    
    def w_i(self, i):
        return self.layers[i].func


def reduce_multiple_polynomial(b: list[field.FQ], c: list[field.FQ], w: polynomial) -> list[field.FQ]:
    assert(len(b) == len(c))
    t = []
    new_poly_terms = []
    for b_i, c_i in zip(b, c):
        new_const = b_i
        gradient = c_i - b_i
        t.append(term(gradient, 1, new_const))
    
    for mono in w.terms:
        new_terms = []
        for each in mono.terms:
            new_term = t[each.x_i - 1] * each.coeff
            new_term.const += each.const
            new_terms.append(new_term)
        new_poly_terms.append(monomial(mono.coeff, new_terms))

    poly = polynomial(new_poly_terms, w.constant)
    return poly.get_all_coefficients()

# reduce verification at two points into verification at a single point
def ell(p1: list[field.FQ], p2: list[field.FQ], t: field.FQ):
    consts = p1
    output = [field.FQ.zero()]*len(p2)
    other_term = [field.FQ.zero()]*len(p2)
    for i in range(len(p2)):
        other_term[i] = p2[i] - consts[i]
    for i in range(len(p2)):
        output[i] = consts[i] + t*other_term[i]
    return output


class Proof:
    def __init__(self, proofs, r, f, D, q, z, r_stars, d, w, adds, mults, k,
                 deltas=None, total_epsilon=None) -> None:
      self.sumcheck_proofs : list[list[list[field.FQ]]] = proofs
      self.sumcheck_r : list[list[field.FQ]] = r
      self.f : list[field.FQ] = f
      self.D : list[list[field.FQ]] = D
      self.q : list[list[field.FQ]] = q
      self.z : list[list[field.FQ]] = z
      self.r : list[field.FQ] = r_stars

      # circuit info
      self.d : int = d
      self.input_func : list[list[field.FQ]] = w
      self.add : list[list[list[field.FQ]]] = adds
      self.mult : list[list[list[field.FQ]]] = mults
      self.k : list[int] = k
      
      # Approximate sumcheck additions
      self.deltas : list[list[field.FQ]] = deltas if deltas else []  # Per-round error bounds
      self.total_epsilon : field.FQ = total_epsilon if total_epsilon else field.FQ.zero()

    def to_dict(self):
        to_serialize = dict()
        to_serialize['sumcheckProof'] = list(map(lambda x: list(map(lambda y: list(map(lambda z: repr(z), y)), x)), self.sumcheck_proofs))
        to_serialize['sumcheckr'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.sumcheck_r))
        to_serialize['f'] = list(map(lambda x: repr(x), self.f))
        to_serialize['q'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.q))
        to_serialize['z'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.z))
        to_serialize['D'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.D))
        to_serialize['r'] = list(map(lambda x: repr(x), self.r))
        to_serialize['inputFunc'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.input_func))
        to_serialize['add'] = list(map(lambda x: list(map(lambda y: list(map(lambda z: repr(z), y)), x)), self.add))
        to_serialize['mult'] = list(map(lambda x: list(map(lambda y: list(map(lambda z: repr(z), y)), x)), self.mult))
        # Add approximate sumcheck fields
        to_serialize['deltas'] = list(map(lambda x: list(map(lambda y: repr(y), x)), self.deltas)) if self.deltas else []
        to_serialize['totalEpsilon'] = repr(self.total_epsilon)
        return to_serialize


class ApproxProof(Proof):
    """
    Extended proof class for approximate sumcheck.
    Includes per-round error bounds and total epsilon tolerance.
    """
    def __init__(self, proofs, r, f, D, q, z, r_stars, d, w, adds, mults, k,
                 deltas, accumulated_errors, total_epsilon):
        super().__init__(proofs, r, f, D, q, z, r_stars, d, w, adds, mults, k, deltas, total_epsilon)
        self.accumulated_errors = accumulated_errors  # Error accumulated per layer


def prove(circuit: Circuit, D, epsilon: field.FQ = field.FQ.zero()):
    """
    Standard GKR prover (backward compatible).
    For approximate proving, use prove_approx instead.
    """
    start_time = time.time()

    D_poly = get_multi_ext(D, circuit.k_i(0))
    z = [[]] * circuit.depth()
    z[0] = [field.FQ.zero()] * circuit.k_i(0)
    sumcheck_proofs = []
    q = []
    f_res = []
    sumcheck_r = []
    r_stars = []

    for i in range(len(z[0])):
        z[0][i] = field.FQ.random() # This initial value is unsafe

    for i in range(circuit.depth() - 1):
        add_i_ext = get_ext(circuit.add_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1))
        for j, r in enumerate(z[i]):
            add_i_ext = add_i_ext.eval_i(r, j + 1)

        mult_i_ext = get_ext(circuit.mult_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1))
        for j, r in enumerate(z[i]):
            mult_i_ext = mult_i_ext.eval_i(r, j + 1)

        w_i_ext_b = get_ext_from_k(circuit.w_i(i + 1), circuit.k_i(i + 1), circuit.k_i(i) + 1)
        w_i_ext_c = get_ext_from_k(circuit.w_i(i + 1), circuit.k_i(i + 1), circuit.k_i(i) + circuit.k_i(i + 1) + 1)

        first = add_i_ext * (w_i_ext_b + w_i_ext_c)
        second = mult_i_ext * w_i_ext_b * w_i_ext_c
        f = first + second

        start_idx = circuit.k_i(i) + 1

        sumcheck_proof, r = prove_sumcheck(f, 2 * circuit.k_i(i + 1), start_idx)
        sumcheck_proofs.append(sumcheck_proof)
        sumcheck_r.append(r)

        b_star = r[0: circuit.k_i(i + 1)]
        c_star = r[circuit.k_i(i + 1):(2 * circuit.k_i(i + 1))]

        next_w = get_ext(circuit.w_i(i + 1), circuit.k_i(i + 1))
        q_i = reduce_multiple_polynomial(b_star, c_star, next_w)

        q.append(q_i)

        f_result = polynomial(f.terms, f.constant)
        f_result_value = field.FQ.zero()
        for j, x in enumerate(r):
            if j == len(r) - 1:
                f_result_value = f_result.eval_univariate(x)
            f_result = f_result.eval_i(x, j + start_idx)
        
        f_res.append(f_result_value)

        r_star = field.FQ(mimc.mimc_hash(list(map(lambda x : int(x), sumcheck_proof[len(sumcheck_proof) - 1]))))
        next_r = ell(b_star, c_star, r_star)
        z[i + 1] = next_r # r_(i + 1)
        r_stars.append(r_star)

    w_input = get_multi_ext(circuit.w_i(circuit.depth() - 1), circuit.k_i(circuit.depth() - 1))
    adds = []
    mults = []
    k = []
    for i in range(circuit.depth() - 1):
        adds.append(get_multi_ext(circuit.add_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1)))
        mults.append(get_multi_ext(circuit.mult_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1)))
        k.append(circuit.k_i(i))
    k.append(circuit.k_i(circuit.depth() - 1))
    proof = Proof(sumcheck_proofs, sumcheck_r, f_res, D_poly, q, z, r_stars, circuit.depth(), w_input, adds, mults, k)
    print("proving time :", time.time() - start_time)
    return proof


def prove_approx(circuit: Circuit, D, max_delta: field.FQ = field.FQ.zero()):
    """
    Approximate GKR prover using approximate sumcheck.
    
    Args:
        circuit: The arithmetic circuit
        D: Output values
        max_delta: Maximum allowed error per sumcheck round
    
    Returns:
        ApproxProof with error bounds
    """
    start_time = time.time()

    D_poly = get_multi_ext(D, circuit.k_i(0))
    z = [[]] * circuit.depth()
    z[0] = [field.FQ.zero()] * circuit.k_i(0)
    sumcheck_proofs = []
    all_deltas = []
    accumulated_errors = []
    q = []
    f_res = []
    sumcheck_r = []
    r_stars = []

    for i in range(len(z[0])):
        z[0][i] = field.FQ.random()

    for i in range(circuit.depth() - 1):
        add_i_ext = get_ext(circuit.add_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1))
        for j, r in enumerate(z[i]):
            add_i_ext = add_i_ext.eval_i(r, j + 1)

        mult_i_ext = get_ext(circuit.mult_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1))
        for j, r in enumerate(z[i]):
            mult_i_ext = mult_i_ext.eval_i(r, j + 1)

        w_i_ext_b = get_ext_from_k(circuit.w_i(i + 1), circuit.k_i(i + 1), circuit.k_i(i) + 1)
        w_i_ext_c = get_ext_from_k(circuit.w_i(i + 1), circuit.k_i(i + 1), circuit.k_i(i) + circuit.k_i(i + 1) + 1)

        first = add_i_ext * (w_i_ext_b + w_i_ext_c)
        second = mult_i_ext * w_i_ext_b * w_i_ext_c
        f = first + second

        start_idx = circuit.k_i(i) + 1
        num_vars = 2 * circuit.k_i(i + 1)

        # Use approximate sumcheck
        approx_proof = prove_approx_sumcheck(f, num_vars, start_idx, max_delta=max_delta)
        
        sumcheck_proofs.append(approx_proof.polynomials)
        sumcheck_r.append(approx_proof.r)
        all_deltas.append(approx_proof.deltas)
        
        r = approx_proof.r
        b_star = r[0: circuit.k_i(i + 1)]
        c_star = r[circuit.k_i(i + 1):(2 * circuit.k_i(i + 1))]

        next_w = get_ext(circuit.w_i(i + 1), circuit.k_i(i + 1))
        q_i = reduce_multiple_polynomial(b_star, c_star, next_w)
        q.append(q_i)

        f_result = polynomial(f.terms, f.constant)
        f_result_value = field.FQ.zero()
        for j, x in enumerate(r):
            if j == len(r) - 1:
                f_result_value = f_result.eval_univariate(x)
            f_result = f_result.eval_i(x, j + start_idx)
        
        f_res.append(f_result_value)

        # Include delta in hash for Fiat-Shamir
        hash_input = list(map(lambda x: int(x), approx_proof.polynomials[-1]))
        hash_input.append(int(max_delta))
        r_star = field.FQ(mimc.mimc_hash(hash_input))
        next_r = ell(b_star, c_star, r_star)
        z[i + 1] = next_r
        r_stars.append(r_star)

    w_input = get_multi_ext(circuit.w_i(circuit.depth() - 1), circuit.k_i(circuit.depth() - 1))
    adds = []
    mults = []
    k = []
    for i in range(circuit.depth() - 1):
        adds.append(get_multi_ext(circuit.add_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1)))
        mults.append(get_multi_ext(circuit.mult_i(i), circuit.k_i(i) + 2 * circuit.k_i(i + 1)))
        k.append(circuit.k_i(i))
    k.append(circuit.k_i(circuit.depth() - 1))
    
    # Calculate total epsilon from all deltas
    total_epsilon = sum([sum(d, field.FQ.zero()) for d in all_deltas], field.FQ.zero())
    
    proof = ApproxProof(
        sumcheck_proofs, sumcheck_r, f_res, D_poly, q, z, r_stars,
        circuit.depth(), w_input, adds, mults, k,
        all_deltas, accumulated_errors, total_epsilon
    )
    print("approximate proving time:", time.time() - start_time)
    return proof


def verify(proof: Proof, epsilon: field.FQ = field.FQ.zero()):
    """
    GKR verifier with optional approximate sumcheck support.
    
    Args:
        proof: The GKR proof
        epsilon: Error tolerance (0 for exact verification)
    
    Returns:
        True if proof is valid (within tolerance), False otherwise
    """
    start = time.time()
    m = [field.FQ.zero()]*proof.d
    m[0] = eval_expansion(proof.D, proof.z[0])

    for i in range(proof.d - 1):
        # Use approximate verification if epsilon > 0
        if int(epsilon) > 0:
            valid = verify_approx_sumcheck_simple(
                m[i], proof.sumcheck_proofs[i], proof.sumcheck_r[i], 
                2 * proof.k[i + 1], epsilon
            )
        else:
            valid = verify_sumcheck(m[i], proof.sumcheck_proofs[i], proof.sumcheck_r[i], 2 * proof.k[i + 1])
        
        if not valid:
            print("verifying time :", time.time() - start)
            return False
        else:
            q_i = proof.q[i]
            q_zero = eval_univariate(q_i, field.FQ.zero())
            q_one = eval_univariate(q_i, field.FQ.one())

            modified_f = eval_expansion(proof.add[i], proof.z[i] + proof.sumcheck_r[i]) * (q_zero + q_one) \
                        + eval_expansion(proof.mult[i], proof.z[i] + proof.sumcheck_r[i]) * (q_zero * q_one)

            sumcheck_p = proof.sumcheck_proofs[i]
            sumcheck_p_hash = field.FQ(mimc.mimc_hash(list(map(lambda x : int(x), sumcheck_p[len(sumcheck_p) - 1]))))

            # For approximate verification, allow some error in f comparison
            if int(epsilon) > 0:
                f_error = abs_field(proof.f[i] - modified_f)
                if int(f_error) > int(epsilon) or sumcheck_p_hash != proof.r[i]:
                    print("verifying time :", time.time() - start)
                    return False
            else:
                if (proof.f[i] != modified_f) or (sumcheck_p_hash != proof.r[i]):
                    print("verifying time :", time.time() - start)
                    return False
            
            m[i + 1] = eval_univariate(q_i, proof.r[i])
    
    # Final check - allow epsilon tolerance for approximate verification
    final_expected = eval_expansion(proof.input_func, proof.z[proof.d - 1])
    if int(epsilon) > 0:
        final_error = abs_field(m[proof.d - 1] - final_expected)
        if int(final_error) > int(epsilon):
            print("verifying time :", time.time() - start)
            return False
    else:
        if m[proof.d - 1] != final_expected:
            print("verifying time :", time.time() - start)
            return False
    
    print("verifying time :", time.time() - start)
    return True


def verify_approx(proof: ApproxProof):
    """
    Approximate GKR verifier for ApproxProof.
    Uses the embedded error bounds from the proof.
    
    Returns:
        (is_valid, total_accumulated_error)
    """
    start = time.time()
    m = [field.FQ.zero()]*proof.d
    m[0] = eval_expansion(proof.D, proof.z[0])
    total_error = field.FQ.zero()

    for i in range(proof.d - 1):
        # Create ApproxSumcheckProof from proof data
        if proof.deltas and len(proof.deltas) > i:
            approx_sumcheck_proof = ApproxSumcheckProof(
                proof.sumcheck_proofs[i],
                proof.deltas[i],
                proof.sumcheck_r[i]
            )
            valid, layer_error = verify_approx_sumcheck(
                m[i], approx_sumcheck_proof, 2 * proof.k[i + 1]
            )
            total_error = total_error + layer_error
        else:
            valid = verify_sumcheck(m[i], proof.sumcheck_proofs[i], proof.sumcheck_r[i], 2 * proof.k[i + 1])
        
        if not valid:
            print("verifying time :", time.time() - start)
            return False, total_error
        
        q_i = proof.q[i]
        q_zero = eval_univariate(q_i, field.FQ.zero())
        q_one = eval_univariate(q_i, field.FQ.one())

        modified_f = eval_expansion(proof.add[i], proof.z[i] + proof.sumcheck_r[i]) * (q_zero + q_one) \
                    + eval_expansion(proof.mult[i], proof.z[i] + proof.sumcheck_r[i]) * (q_zero * q_one)

        sumcheck_p = proof.sumcheck_proofs[i]
        
        # Include delta in hash check for approximate proofs
        if proof.deltas and len(proof.deltas) > i:
            hash_input = list(map(lambda x: int(x), sumcheck_p[-1]))
            hash_input.append(int(proof.deltas[i][-1]))
            sumcheck_p_hash = field.FQ(mimc.mimc_hash(hash_input))
        else:
            sumcheck_p_hash = field.FQ(mimc.mimc_hash(list(map(lambda x: int(x), sumcheck_p[-1]))))

        f_error = abs_field(proof.f[i] - modified_f)
        if int(f_error) > int(proof.total_epsilon) or sumcheck_p_hash != proof.r[i]:
            print("verifying time :", time.time() - start)
            return False, total_error
        
        total_error = total_error + f_error
        m[i + 1] = eval_univariate(q_i, proof.r[i])

    final_expected = eval_expansion(proof.input_func, proof.z[proof.d - 1])
    final_error = abs_field(m[proof.d - 1] - final_expected)
    total_error = total_error + final_error
    
    if int(total_error) > int(proof.total_epsilon):
        print("verifying time :", time.time() - start)
        return False, total_error
    
    print("verifying time :", time.time() - start)
    return True, total_error
