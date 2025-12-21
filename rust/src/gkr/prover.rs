use super::{poly::*, sumcheck::*, GKRCircuit, Input, Proof};
use ff::PrimeField;
use mimc_rs::{Fr, Mimc7};
use std::vec;

pub fn prove<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    circuit: &GKRCircuit<S>,
    input: &Input<S>,
) -> Proof<S> {
    let mimc = Mimc7::new(91);

    let mut sumcheck_proofs = vec![];
    let mut sumcheck_r = vec![];
    let mut sumcheck_deltas = vec![];
    let mut sumcheck_error_signs = vec![];
    let mut q = vec![];
    let mut r_stars = vec![];
    let mut z_zero = vec![];
    for _ in 0..circuit.layer[0].k {
        z_zero.push(S::zero());
    }
    let mut z = vec![];
    z.push(z_zero);

    for i in 0..circuit.depth() {
        let add = circuit.add(i);
        let mut add_res = vec![];
        if z[i].len() == 0 {
            add_res = add.clone();
        } else {
            add_res = partial_eval_binary_form(&add, &z[i]);
        }
        let mult = circuit.mult(i);
        let mut mult_res = vec![];
        if z[i].len() == 0 {
            mult_res = mult.clone();
        } else {
            mult_res = partial_eval_binary_form(&mult, &z[i]);
        }
        let w_i = input.w(i + 1).clone();
        let mut w_i_ext_b = vec![];
        for t in w_i.iter() {
            w_i_ext_b.push(extend_length(t, 2 * circuit.k(i + 1) + 1));
        }
        let mut w_i_ext_c = modify_poly_from_k(&input.w(i + 1), circuit.k(i + 1));

        if w_i_ext_b.len() == 0 {
            w_i_ext_b = vec![vec![S::zero(); 2 * circuit.k(i + 1) + 1]];
        }
        if w_i_ext_c.len() == 0 {
            w_i_ext_c = vec![vec![S::zero(); 2 * circuit.k(i + 1) + 1]];
        }

        let (sumcheck_proof, r) = prove_sumcheck_opt(
            &circuit.add_wire(i),
            &circuit.mult_wire(i),
            &add_res,
            &mult_res,
            &w_i_ext_b,
            &w_i_ext_c,
            2 * circuit.k(i + 1),
        );
        sumcheck_proofs.push(sumcheck_proof.clone());
        sumcheck_r.push(r.clone());
        // Default to exact-mode deltas/signs (all zeros). Approx mode will overwrite.
        sumcheck_deltas.push(vec![S::zero(); sumcheck_proof.len()]);
        sumcheck_error_signs.push(vec![S::zero(); sumcheck_proof.len()]);

        let mut b_star = vec![];
        let mut c_star = vec![];
        b_star.extend_from_slice(&r[..circuit.k(i + 1)]);
        c_star.extend_from_slice(&r[circuit.k(i + 1)..]);

        let next_w = input.w(i + 1);
        let q_i = reduce_multiple_polynomial(&b_star, &c_star, &next_w);

        q.push(q_i);

        let mimc_r_star = sumcheck_proof[sumcheck_proof.len() - 1]
            .iter()
            .map(|s| convert_s_to_fr(s))
            .collect();
        let r_star: S = convert_fr_to_s(mimc.multi_hash(mimc_r_star, &Fr::from(0)));

        let next_r = l_function(&b_star, &c_star, &r_star);
        z.push(next_r);
        r_stars.push(r_star);
    }

    Proof {
        sumcheck_proofs,
        sumcheck_r,
        sumcheck_deltas,
        sumcheck_error_signs,
        d: input.d.clone(),
        q,
        z,
        r: r_stars,
        depth: circuit.depth() + 1,
        input_func: input.w(circuit.depth()),
        k: circuit.get_k_list(),
    }
}

/// Approximate-mode prover: uses approximate sumcheck (with per-round deltas) and
/// computes Circom-friendly `errorSigns` hints for absolute-error checks.
pub fn prove_approx<S: PrimeField<Repr = [u8; 32]> + std::hash::Hash>(
    circuit: &GKRCircuit<S>,
    input: &Input<S>,
    max_delta: S,
) -> Proof<S> {
    let mimc = Mimc7::new(91);

    let mut sumcheck_proofs = vec![];
    let mut sumcheck_r = vec![];
    let mut sumcheck_deltas = vec![];
    let mut sumcheck_error_signs = vec![];
    let mut q = vec![];
    let mut r_stars = vec![];

    // Claim for the first sumcheck instance (matches verifier.circom).
    let mut claim = S::zero();

    let mut z_zero = vec![];
    for _ in 0..circuit.layer[0].k {
        z_zero.push(S::zero());
    }
    let mut z = vec![];
    z.push(z_zero);

    for i in 0..circuit.depth() {
        let add = circuit.add(i);
        let add_res = if z[i].len() == 0 {
            add.clone()
        } else {
            partial_eval_binary_form(&add, &z[i])
        };

        let mult = circuit.mult(i);
        let mult_res = if z[i].len() == 0 {
            mult.clone()
        } else {
            partial_eval_binary_form(&mult, &z[i])
        };

        let w_i = input.w(i + 1).clone();
        let mut w_i_ext_b = vec![];
        for t in w_i.iter() {
            w_i_ext_b.push(extend_length(t, 2 * circuit.k(i + 1) + 1));
        }
        let mut w_i_ext_c = modify_poly_from_k(&input.w(i + 1), circuit.k(i + 1));

        if w_i_ext_b.len() == 0 {
            w_i_ext_b = vec![vec![S::zero(); 2 * circuit.k(i + 1) + 1]];
        }
        if w_i_ext_c.len() == 0 {
            w_i_ext_c = vec![vec![S::zero(); 2 * circuit.k(i + 1) + 1]];
        }

        // Approximate sumcheck for this layer
        let approx = prove_approx_sumcheck_opt(
            &circuit.add_wire(i),
            &circuit.mult_wire(i),
            &add_res,
            &mult_res,
            &w_i_ext_b,
            &w_i_ext_c,
            2 * circuit.k(i + 1),
            max_delta,
        );

        // Circom-friendly error sign hints (0/1)
        let signs = compute_error_signs(claim, &approx.polynomials, &approx.r);

        sumcheck_proofs.push(approx.polynomials.clone());
        sumcheck_r.push(approx.r.clone());
        sumcheck_deltas.push(approx.deltas.clone());
        sumcheck_error_signs.push(signs);

        let mut b_star = vec![];
        let mut c_star = vec![];
        b_star.extend_from_slice(&approx.r[..circuit.k(i + 1)]);
        c_star.extend_from_slice(&approx.r[circuit.k(i + 1)..]);

        let next_w = input.w(i + 1);
        let q_i = reduce_multiple_polynomial(&b_star, &c_star, &next_w);
        q.push(q_i.clone());

        // r_star: bind max_delta into the transcript (defensive, aligns with the python path)
        let mut mimc_r_star: Vec<Fr> = approx.polynomials[approx.polynomials.len() - 1]
            .iter()
            .map(|s| convert_s_to_fr(s))
            .collect();
        mimc_r_star.push(convert_s_to_fr(&max_delta));
        let r_star: S = convert_fr_to_s(mimc.multi_hash(mimc_r_star, &Fr::from(0)));

        let next_r = l_function(&b_star, &c_star, &r_star);
        z.push(next_r);
        r_stars.push(r_star);

        // Claim for next layer equals q_i(r_star) (matches verifier.circom's m[i].result)
        claim = eval_univariate(&q_i, &r_star);
    }

    Proof {
        sumcheck_proofs,
        sumcheck_r,
        sumcheck_deltas,
        sumcheck_error_signs,
        d: input.d.clone(),
        q,
        z,
        r: r_stars,
        depth: circuit.depth() + 1,
        input_func: input.w(circuit.depth()),
        k: circuit.get_k_list(),
    }
}
