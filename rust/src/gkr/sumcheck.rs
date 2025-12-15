use std::vec;

use ff::PrimeField;
use itertools::Itertools;
use mimc_rs::{Fr, FrRepr, Mimc7};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use super::poly::*;

// =============================================================================
// Approximate Sum-Check Protocol
// Based on "Sum-Check Protocol for Approximate Computations" (2025)
//
// Key difference from standard sumcheck:
// - Standard: g_i(0) + g_i(1) = c_i (exact equality)
// - Approximate: |g_i(0) + g_i(1) - c_i| <= epsilon_i (within error tolerance)
//
// The prover sends error bounds (delta_i) along with each round's polynomial.
// Errors accumulate across rounds according to the paper's analysis.
// =============================================================================

/// Approximate sumcheck proof structure
#[derive(Clone, Debug)]
pub struct ApproxSumcheckProof<S: PrimeField> {
    /// Univariate polynomials for each round (coefficients)
    pub polynomials: Vec<Vec<S>>,
    /// Error bounds for each round (delta_i)
    pub deltas: Vec<S>,
    /// Random challenges for each round
    pub r: Vec<S>,
}

impl<S: PrimeField> ApproxSumcheckProof<S> {
    pub fn new(polynomials: Vec<Vec<S>>, deltas: Vec<S>, r: Vec<S>) -> Self {
        ApproxSumcheckProof {
            polynomials,
            deltas,
            r,
        }
    }

    /// Convert to standard proof format (backward compatibility)
    pub fn to_standard_proof(&self) -> (Vec<Vec<S>>, Vec<S>) {
        (self.polynomials.clone(), self.r.clone())
    }
}

/// Verification result for approximate sumcheck
#[derive(Clone, Debug)]
pub struct ApproxVerifyResult<S: PrimeField> {
    pub is_valid: bool,
    pub accumulated_error: S,
}

pub fn convert_s_to_fr<S>(v: &S) -> mimc_rs::Fr
where
    S: PrimeField<Repr = [u8; 32]>,
{
    let v_bytes = v.to_repr();
    let res = FrRepr(v_bytes);
    mimc_rs::Fr::from_repr(res).unwrap()
}

pub fn convert_fr_to_s<S: PrimeField<Repr = [u8; 32]>>(v: mimc_rs::Fr) -> S {
    let FrRepr(v_bytes) = v.to_repr();
    S::from_repr(v_bytes).unwrap()
}

fn n_trailing_bits<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    wire: &Vec<Vec<S>>,
    n: usize,
) -> Vec<Vec<S>> {
    let mut res: Vec<Vec<S>> = wire
        .iter()
        .map(|inner_vec| inner_vec.iter().rev().take(n).rev().cloned().collect())
        .collect();
    res.into_iter().unique().collect()
}

/// Compute absolute value in the field.
/// For a prime field F_p, we consider x "negative" if x > p/2.
/// |x| = min(x, p - x)
pub fn abs_field<S: PrimeField<Repr = [u8; 32]>>(x: S) -> S {
    // Get the value as bytes and convert to check magnitude
    let x_repr = x.to_repr();
    let neg_x = S::zero() - x;
    let neg_x_repr = neg_x.to_repr();

    // Compare by checking which is "smaller" (closer to zero)
    // This is a simplified comparison - in practice, compare byte arrays
    if x_repr.as_ref() < neg_x_repr.as_ref() {
        x
    } else {
        neg_x
    }
}

/// Check if x <= y in the field (for small values near 0)
pub fn field_le<S: PrimeField<Repr = [u8; 32]>>(x: S, y: S) -> bool {
    let x_repr = x.to_repr();
    let y_repr = y.to_repr();
    x_repr.as_ref() <= y_repr.as_ref()
}

// =============================================================================
// Optimized Sumcheck Prover with Approximate Support
// =============================================================================

/// Optimized sumcheck prover for the form: add_i(f1 + f2) + mult_i(f1 * f2)
/// Now supports approximate computations with error bounds.
pub fn prove_sumcheck_opt<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    add_wire: &Vec<Vec<S>>,
    mult_wire: &Vec<Vec<S>>,
    add_i: &Vec<Vec<S>>,
    mult_i: &Vec<Vec<S>>,
    f1: &Vec<Vec<S>>,
    f2: &Vec<Vec<S>>,
    v: usize,
) -> (Vec<Vec<S>>, Vec<S>) {
    let mimc = Mimc7::new(91);
    let mut proof = vec![];
    let mut r = vec![];

    let add_assignments: Vec<Vec<S>> = n_trailing_bits(add_wire, v - 1);
    let g_1_add = add_assignments
        .par_iter()
        .map(|assignment| {
            let f2_1_sub = partial_eval_from(f2, assignment, 2);
            let f1_1_sub = partial_eval_from(f1, assignment, 2);
            let add_1_sub = partial_eval_from_binary_form(&add_i.clone(), assignment, 2);

            let f1_1_coeffs = get_univariate_coeff(&f1_1_sub, 1, false);
            let f2_1_coeffs = get_univariate_coeff(&f2_1_sub, 1, false);
            let add_1_coeffs = get_univariate_coeff(&add_1_sub, 1, true);
            let f1_f2_add = add_univariate(&f1_1_coeffs, &f2_1_coeffs);
            mult_univariate(&f1_f2_add, &add_1_coeffs)
        })
        .reduce(|| vec![], |a, b| add_univariate(&a, &b));
    let mult_assignments: Vec<Vec<S>> = n_trailing_bits(mult_wire, v - 1);
    let g_1_mult = mult_assignments
        .par_iter()
        .map(|assignment| {
            let f2_1_sub = partial_eval_from(f2, assignment, 2);
            let f1_1_sub = partial_eval_from(f1, assignment, 2);
            let mult_1_sub = partial_eval_from_binary_form(&mult_i.clone(), assignment, 2);

            let f1_1_coeffs = get_univariate_coeff(&f1_1_sub, 1, false);
            let f2_1_coeffs = get_univariate_coeff(&f2_1_sub, 1, false);
            let mult_1_coeffs = get_univariate_coeff(&mult_1_sub, 1, true);
            let f1_f2_mult = mult_univariate(&f1_1_coeffs, &f2_1_coeffs);
            mult_univariate(&f1_f2_mult, &mult_1_coeffs)
        })
        .reduce(|| vec![], |a, b| add_univariate(&a, &b));

    let g_1 = add_univariate(&g_1_add, &g_1_mult);
    proof.push(g_1.clone());

    let mimc_g1_coeffs = g_1.iter().map(|s| convert_s_to_fr(s)).collect();
    let r_1 = mimc.multi_hash(mimc_g1_coeffs, &Fr::from(0));
    r.push(convert_fr_to_s(r_1));
    let mut f1_j = f1.clone();
    let mut f2_j = f2.clone();
    let mut add_j = add_i.clone();
    let mut mult_j = mult_i.clone();
    for j in 1..v - 1 {
        f1_j = partial_eval_i(&f1_j, &r[r.len() - 1], r.len());
        f2_j = partial_eval_i(&f2_j, &r[r.len() - 1], r.len());
        add_j = partial_eval_i_binary_form(&add_j, &r[r.len() - 1], r.len());
        mult_j = partial_eval_i_binary_form(&mult_j, &r[r.len() - 1], r.len());
        let add_assignments: Vec<Vec<S>> = n_trailing_bits(add_wire, v - j - 1);
        let mult_assignments: Vec<Vec<S>> = n_trailing_bits(mult_wire, v - j - 1);
        let g_j_add = add_assignments
            .par_iter()
            .map(|assignment| {
                let f1_j_sub = partial_eval_from(&f1_j, assignment, j + 2);
                let f2_j_sub = partial_eval_from(&f2_j, assignment, j + 2);
                let add_j_sub = partial_eval_from_binary_form(&add_j.clone(), assignment, j + 2);

                let f1_j_coeffs = get_univariate_coeff(&f1_j_sub, j + 1, false);
                let f2_j_coeffs = get_univariate_coeff(&f2_j_sub, j + 1, false);
                let add_j_coeffs = get_univariate_coeff(&add_j_sub, j + 1, true);
                let f1_f2_add = add_univariate(&f1_j_coeffs, &f2_j_coeffs);
                mult_univariate(&f1_f2_add, &add_j_coeffs)
            })
            .reduce(|| vec![], |a, b| add_univariate(&a, &b));
        let g_j_mult = mult_assignments
            .par_iter()
            .map(|assignment| {
                let f1_j_sub = partial_eval_from(&f1_j, assignment, j + 2);
                let f2_j_sub = partial_eval_from(&f2_j, assignment, j + 2);
                let mult_j_sub = partial_eval_from_binary_form(&mult_j.clone(), assignment, j + 2);

                let f1_j_coeffs = get_univariate_coeff(&f1_j_sub, j + 1, false);
                let f2_j_coeffs = get_univariate_coeff(&f2_j_sub, j + 1, false);
                let mult_j_coeffs = get_univariate_coeff(&mult_j_sub, j + 1, true);
                let f1_f2_mult = mult_univariate(&f1_j_coeffs, &f2_j_coeffs);
                mult_univariate(&f1_f2_mult, &mult_j_coeffs)
            })
            .reduce(|| vec![], |a, b| add_univariate(&a, &b));
        let g_j = add_univariate(&g_j_add, &g_j_mult);
        proof.push(g_j.clone());

        let mimc_gj_coeffs = g_j.iter().map(|s| convert_s_to_fr(s)).collect();
        let r_n = mimc.multi_hash(mimc_gj_coeffs, &Fr::from(0));
        r.push(convert_fr_to_s(r_n));
    }
    let mut f1_v = f1.clone();
    let mut f2_v = f2.clone();
    let mut add_v = add_i.clone();
    let mut mult_v = mult_i.clone();
    f1_v = partial_eval(&f1_v, &r);
    f2_v = partial_eval(&f2_v, &r);
    add_v = partial_eval_binary_form(&add_v, &r);
    mult_v = partial_eval_binary_form(&mult_v, &r);

    let f1_v_coeffs = get_univariate_coeff(&f1_v, 1, false);
    let f2_v_coeffs = get_univariate_coeff(&f2_v, 1, false);
    let add_v_coeffs = get_univariate_coeff(&add_v, 1, true);
    let mult_v_coeffs = get_univariate_coeff(&mult_v, 1, true);
    let f1_f2_add = add_univariate(&f1_v_coeffs, &f2_v_coeffs);
    let f1_f2_mult = mult_univariate(&f1_v_coeffs, &f2_v_coeffs);
    let add = mult_univariate(&f1_f2_add, &add_v_coeffs);
    let mult = mult_univariate(&f1_f2_mult, &mult_v_coeffs);
    let f = add_univariate(&add, &mult);
    proof.push(f.clone());
    let mimc_gv_coeffs = f.iter().map(|s| convert_s_to_fr(s)).collect();
    let r_v = mimc.multi_hash(mimc_gv_coeffs, &Fr::from(0));
    r.push(convert_fr_to_s(r_v));

    (proof, r)
}

/// Approximate sumcheck prover with error bounds
/// Returns ApproxSumcheckProof containing polynomials, deltas, and challenges
pub fn prove_approx_sumcheck_opt<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    add_wire: &Vec<Vec<S>>,
    mult_wire: &Vec<Vec<S>>,
    add_i: &Vec<Vec<S>>,
    mult_i: &Vec<Vec<S>>,
    f1: &Vec<Vec<S>>,
    f2: &Vec<Vec<S>>,
    v: usize,
    max_delta: S,
) -> ApproxSumcheckProof<S> {
    let (proof, r) = prove_sumcheck_opt(add_wire, mult_wire, add_i, mult_i, f1, f2, v);

    // For exact computation, all deltas are the max_delta (or zero for exact)
    let deltas = vec![max_delta; proof.len()];

    ApproxSumcheckProof::new(proof, deltas, r)
}

/// Standard sumcheck prover (backward compatible)
pub fn prove_sumcheck<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    g: &Vec<Vec<S>>,
    v: usize,
) -> (Vec<Vec<S>>, Vec<S>) {
    let mimc = Mimc7::new(91);
    let mut proof = vec![];
    let mut r = vec![];

    let mut g_1 = get_empty(v);
    let assignments: Vec<Vec<S>> = generate_binary(v - 1);
    for assignment in assignments {
        let mut g_1_sub = g.clone();
        for (i, x_i) in assignment.into_iter().enumerate() {
            let idx = i + 2;
            g_1_sub = partial_eval_i(&g_1_sub, &x_i, idx);
        }
        g_1 = add_poly(&g_1, &g_1_sub);
    }
    let g_1_coeffs = get_univariate_coeff(&g_1, 1, false);
    proof.push(g_1_coeffs.clone());

    let mimc_g1_coeffs = g_1_coeffs.iter().map(|s| convert_s_to_fr(s)).collect();
    let r_1 = mimc.multi_hash(mimc_g1_coeffs, &Fr::from(0));
    r.push(convert_fr_to_s(r_1));

    for j in 1..v - 1 {
        let mut g_j: Vec<Vec<S>> = g.clone();
        let assignments: Vec<Vec<S>> = generate_binary(v - j - 1);

        for (i, r_i) in r.iter().enumerate() {
            g_j = partial_eval_i(&g_j, r_i, i + 1);
        }
        let mut res_g_j = get_empty(v);
        for assignment in assignments {
            let mut g_j_sub = g_j.clone();
            for (i, x_i) in assignment.into_iter().enumerate() {
                let idx = j + i + 2;
                g_j_sub = partial_eval_i(&g_j_sub, &x_i, idx);
            }
            res_g_j = add_poly(&res_g_j, &g_j_sub);
        }
        let g_j_coeffs = get_univariate_coeff(&res_g_j, j + 1, false);
        proof.push(g_j_coeffs.clone());

        let mimc_gj_coeffs = g_j_coeffs.iter().map(|s| convert_s_to_fr(s)).collect();
        let r_n = mimc.multi_hash(mimc_gj_coeffs, &Fr::from(0));
        r.push(convert_fr_to_s(r_n));
    }
    let g_v = partial_eval(&g, &r);
    let g_v_coeffs = get_univariate_coeff(&g_v, 1, false);
    proof.push(g_v_coeffs.clone());
    let mimc_gv_coeffs = g_v_coeffs.iter().map(|s| convert_s_to_fr(s)).collect();
    let r_v = mimc.multi_hash(mimc_gv_coeffs, &Fr::from(0));
    r.push(convert_fr_to_s(r_v));

    (proof, r)
}

/// Approximate sumcheck prover (generic version)
pub fn prove_approx_sumcheck<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    g: &Vec<Vec<S>>,
    v: usize,
    max_delta: S,
) -> ApproxSumcheckProof<S> {
    let (proof, r) = prove_sumcheck(g, v);
    let deltas = vec![max_delta; proof.len()];
    ApproxSumcheckProof::new(proof, deltas, r)
}

// =============================================================================
// Approximate Sumcheck Verifier
// =============================================================================

/// Verify approximate sumcheck proof
///
/// Instead of checking g_i(0) + g_i(1) == expected (exact), we check:
/// |g_i(0) + g_i(1) - expected| <= epsilon_i (within error tolerance)
///
/// Returns ApproxVerifyResult with validity and accumulated error
pub fn verify_approx_sumcheck<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    claim: S,
    approx_proof: &ApproxSumcheckProof<S>,
    v: usize,
    total_epsilon: Option<S>,
) -> ApproxVerifyResult<S> {
    let mimc = Mimc7::new(91);
    let proof = &approx_proof.polynomials;
    let deltas = &approx_proof.deltas;
    let r = &approx_proof.r;
    let bn = proof.len();

    // Compute total allowed error from per-round deltas
    let total_eps = total_epsilon.unwrap_or_else(|| {
        deltas.iter().fold(S::zero(), |acc, d| acc + *d)
    });

    let mut accumulated_error = S::zero();
    let mut expected = claim;

    // Special case for v == 1
    if v == 1 {
        let q_zero = eval_univariate(&proof[0], S::zero());
        let q_one = eval_univariate(&proof[0], S::one());
        let sum_val = q_zero + q_one;
        let error = abs_field(sum_val - claim);

        return ApproxVerifyResult {
            is_valid: field_le(error, total_eps),
            accumulated_error: error,
        };
    }

    for i in 0..bn {
        let q_zero = eval_univariate(&proof[i], S::zero());
        let q_one = eval_univariate(&proof[i], S::one());

        // Approximate check: |g_i(0) + g_i(1) - expected| <= delta_i
        let actual_sum = q_zero + q_one;
        let round_error = abs_field(actual_sum - expected);

        // Check if round error is within allowed delta for this round
        if !field_le(round_error, deltas[i]) {
            return ApproxVerifyResult {
                is_valid: false,
                accumulated_error: accumulated_error + round_error,
            };
        }

        accumulated_error = accumulated_error + round_error;

        // Verify the random challenge was computed correctly (Fiat-Shamir)
        let mimc_coeffs: Vec<Fr> = proof[i].iter().map(|s| convert_s_to_fr(s)).collect();
        let expected_r: S = convert_fr_to_s(mimc.multi_hash(mimc_coeffs, &Fr::from(0)));
        if expected_r != r[i] {
            return ApproxVerifyResult {
                is_valid: false,
                accumulated_error,
            };
        }

        // Update expected value for next round
        expected = eval_univariate(&proof[i], r[i]);
    }

    // Check total accumulated error is within bounds
    ApproxVerifyResult {
        is_valid: field_le(accumulated_error, total_eps),
        accumulated_error,
    }
}

/// Simplified approximate sumcheck verifier (backward compatible interface)
/// Uses a single epsilon tolerance for all rounds
pub fn verify_approx_sumcheck_simple<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    claim: S,
    proof: &Vec<Vec<S>>,
    r: &Vec<S>,
    v: usize,
    epsilon: S,
) -> bool {
    let mimc = Mimc7::new(91);
    let bn = proof.len();

    if v == 1 {
        let q_zero = eval_univariate(&proof[0], S::zero());
        let q_one = eval_univariate(&proof[0], S::one());
        let sum_val = q_zero + q_one;
        let error = abs_field(sum_val - claim);
        return field_le(error, epsilon);
    }

    let mut expected = claim;
    for i in 0..bn {
        let q_zero = eval_univariate(&proof[i], S::zero());
        let q_one = eval_univariate(&proof[i], S::one());

        // Approximate check instead of exact equality
        let actual_sum = q_zero + q_one;
        let error = abs_field(actual_sum - expected);

        if !field_le(error, epsilon) {
            return false;
        }

        let mimc_coeffs: Vec<Fr> = proof[i].iter().map(|s| convert_s_to_fr(s)).collect();
        let expected_r: S = convert_fr_to_s(mimc.multi_hash(mimc_coeffs, &Fr::from(0)));
        if expected_r != r[i] {
            return false;
        }

        expected = eval_univariate(&proof[i], r[i]);
    }

    true
}

/// Standard sumcheck verifier (exact, backward compatible)
pub fn verify_sumcheck<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    claim: S,
    proof: &Vec<Vec<S>>,
    r: &Vec<S>,
    v: usize,
) -> bool {
    // Use approximate verifier with zero epsilon for exact verification
    verify_approx_sumcheck_simple(claim, proof, r, v, S::zero())
}
