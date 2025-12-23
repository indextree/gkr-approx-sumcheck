use std::{env::current_dir, fs::File, io::Read, path::PathBuf, process::Command, time::Instant};

use crate::{
    convert::{convert_r1cs_wtns_gkr, Output},
    file_utils::{execute_circom, get_name, stringify_fr, write_aggregated_input, write_output},
    gkr::{prover, GKRCircuit, Input, Proof},
};
use colored::Colorize;
use halo2curves::bn256::Fr;
use r1cs_file::*;
use serde::{Deserialize, Serialize};
use tera::{Context, Tera};
use wtns_file::*;

use rayon::prelude::*;

/// Circom-GKR
struct Meta(Vec<usize>);

#[derive(Serialize, Deserialize, Debug, Clone)]
#[allow(non_snake_case)]
pub struct CircomInputProof {
    pub sumcheckProof: Vec<Vec<Vec<String>>>,
    pub sumcheckr: Vec<Vec<String>>,
    pub sumcheckDeltas: Vec<Vec<String>>,
    pub sumcheckErrorSigns: Vec<Vec<String>>,
    pub q: Vec<Vec<String>>,
    pub D: Vec<Vec<String>>,
    pub z: Vec<Vec<String>>,
    pub r: Vec<String>,
    pub inputFunc: Vec<Vec<String>>,
}

impl CircomInputProof {
    pub fn empty() -> Self {
        let zero = String::from("0");
        let sp = vec![vec![vec![zero.clone()]]];
        let q = vec![vec![zero.clone()]];
        let sr = vec![vec![zero.clone()]];
        let f = vec![zero.clone()];
        CircomInputProof {
            sumcheckProof: sp.clone(),
            sumcheckr: sr,
            sumcheckDeltas: vec![vec![zero.clone()]],
            sumcheckErrorSigns: vec![vec![zero.clone()]],
            q: q.clone(),
            D: q.clone(),
            z: q.clone(),
            r: f.clone(),
            inputFunc: q.clone(),
        }
    }

    fn new_from_proof(proof: Proof<Fr>) -> Self {
        let sp: Vec<Vec<Vec<String>>> = proof
            .sumcheck_proofs
            .iter()
            .map(|p| p.iter().map(|f| stringify_fr_vector(f)).collect())
            .collect();

        let sr: Vec<Vec<String>> = proof
            .sumcheck_r
            .iter()
            .map(|p| stringify_fr_vector(p))
            .collect();

        let deltas: Vec<Vec<String>> = proof
            .sumcheck_deltas
            .iter()
            .map(|p| stringify_fr_vector(p))
            .collect();
        let error_signs: Vec<Vec<String>> = proof
            .sumcheck_error_signs
            .iter()
            .map(|p| stringify_fr_vector(p))
            .collect();

        let q: Vec<Vec<String>> = proof.q.iter().map(|p| stringify_fr_vector(p)).collect();
        let d: Vec<Vec<String>> = proof.d.iter().map(|p| stringify_fr_vector(p)).collect();
        let z: Vec<Vec<String>> = proof.z.iter().map(|p| stringify_fr_vector(p)).collect();
        let r: Vec<String> = stringify_fr_vector(&proof.r);
        let input_func: Vec<Vec<String>> = proof
            .input_func
            .iter()
            .map(|p| stringify_fr_vector(p))
            .collect();

        CircomInputProof {
            sumcheckProof: sp,
            sumcheckr: sr,
            sumcheckDeltas: deltas,
            sumcheckErrorSigns: error_signs,
            q,
            D: d,
            z,
            r,
            inputFunc: input_func,
        }
    }
}

fn stringify_fr_vector(v: &Vec<Fr>) -> Vec<String> {
    v.iter().map(|f| stringify_fr(f)).collect()
}

fn zeros(l: usize) -> Vec<Fr> {
    vec![Fr::zero(); l]
}

fn prove_one(circuit: &GKRCircuit<Fr>, input: &Input<Fr>, max_delta: Option<Fr>) -> Proof<Fr> {
    match max_delta {
        Some(d) => prover::prove_approx(circuit, input, d),
        None => prover::prove(circuit, input),
    }
}

fn get_meta(proofs: &Vec<Proof<Fr>>) -> Vec<Meta> {
    let mut meta_infos = vec![];
    for proof in proofs {
        let mut meta = vec![];
        // meta[0] = depth
        meta.push(proof.depth);

        // meta[1] = largest k
        let largest_k = proof
            .k
            .iter()
            .max()
            .cloned()
            .expect("Empty proof : k is None");
        meta.push(largest_k);

        // meta[2] = k_i(0)
        meta.push(proof.k[0]);

        // meta[3] = # of terms of D
        //
        // NOTE: In Circom(2.x), if a zero-length array (e.g. `signal input D[0][...]`) exists,
        // a divide-by-zero panic has been observed during the `build_io_map` stage.
        // The current `VerifyGKR` template in `verifier.circom` does not use `D`,
        // so we force meta[3] to be at least 1 and pad `Proof.d` with zeros accordingly.
        let n_terms_d = proof.d.len().max(1);
        meta.push(n_terms_d);

        // meta[4] = largest # of terms among sumcheck proofs (highest degree)
        let largest_deg = proof
            .sumcheck_proofs
            .iter()
            .map(|p| p.iter().map(|terms| terms.len()).max().unwrap())
            .max()
            .unwrap();
        meta.push(largest_deg);

        // meta[5] = largest # of terms among q
        let largest_terms_q = proof.q.iter().map(|p| p.len()).max().unwrap();
        meta.push(largest_terms_q);

        // meta[6] = # of terms in w_d
        let n_terms_input_func = proof.input_func.len();
        meta.push(n_terms_input_func);

        // meta[7] = k_i(d - 1)
        let k_input = proof.k[proof.depth - 1];
        meta.push(k_input);

        meta.append(&mut proof.k.clone());

        meta_infos.push(Meta(meta));
    }
    meta_infos
}

fn modify_proof_for_circom(proof: &Vec<Proof<Fr>>, meta_value: &Vec<Meta>) -> Vec<Proof<Fr>> {
    let mut proofs = vec![];
    for (pr, m) in proof.iter().zip(meta_value.iter()) {
        let meta = m.0.clone();
        let mut sumcheck_proofs = vec![];
        for p in pr.sumcheck_proofs.iter() {
            let mut new_p = vec![];
            for terms in p.iter() {
                let mut new_terms = terms.clone();
                if terms.len() < meta[4] {
                    let mut z = zeros(meta[4] - terms.len());
                    z.append(&mut new_terms);
                    new_p.push(z);
                } else {
                    new_p.push(new_terms);
                }
            }
            if p.len() < 2 * meta[1] {
                for _ in 0..(2 * meta[1] - p.len()) {
                    let new_terms = zeros(meta[4]);
                    new_p.push(new_terms);
                }
            }
            sumcheck_proofs.push(new_p);
        }

        let mut sumcheck_r = vec![];
        for p in pr.sumcheck_r.iter() {
            let mut new_p = p.clone();
            if p.len() < 2 * meta[1] {
                new_p.extend(zeros(2 * meta[1] - p.len()));
            }
            sumcheck_r.push(new_p);
        }

        let mut sumcheck_deltas = vec![];
        for p in pr.sumcheck_deltas.iter() {
            let mut new_p = p.clone();
            if p.len() < 2 * meta[1] {
                new_p.extend(zeros(2 * meta[1] - p.len()));
            }
            sumcheck_deltas.push(new_p);
        }

        let mut sumcheck_error_signs = vec![];
        for p in pr.sumcheck_error_signs.iter() {
            let mut new_p = p.clone();
            if p.len() < 2 * meta[1] {
                new_p.extend(zeros(2 * meta[1] - p.len()));
            }
            sumcheck_error_signs.push(new_p);
        }

        let mut q = vec![];
        for p in pr.q.iter() {
            let mut new_p = p.clone();
            if p.len() < meta[5] {
                let mut z = zeros(meta[5] - p.len());
                z.append(&mut new_p);
                q.push(z);
            } else {
                q.push(new_p);
            }
        }

        let mut z = vec![];
        for p in pr.z.iter() {
            let mut new_p = p.clone();
            if p.len() < meta[1] {
                new_p.extend(zeros(meta[1] - p.len()));
            }
            z.push(new_p);
        }

        // D (meta[3] x (meta[2] + 1)) is currently unused in verifier.circom,
        // but Circom panics on zero-length arrays, so we pad it to at least 1 row.
        let mut d = pr.d.clone();
        let d_rows = meta[3];
        let d_cols = meta[2] + 1;
        for row in d.iter_mut() {
            if row.len() < d_cols {
                row.extend(zeros(d_cols - row.len()));
            }
        }
        if d.len() < d_rows {
            for _ in 0..(d_rows - d.len()) {
                d.push(zeros(d_cols));
            }
        }

        let new_p = Proof {
            sumcheck_proofs,
            sumcheck_r,
            sumcheck_deltas,
            sumcheck_error_signs,
            q,
            z,
            d,
            r: pr.r.clone(),
            depth: pr.depth,
            input_func: pr.input_func.clone(),
            k: pr.k.clone(),
        };
        proofs.push(new_p);
    }
    proofs
}

fn modify_circom_file(path: String, meta_value: &Vec<Meta>) -> String {
    let mut added = Tera::default();
    let total = format!("{}", meta_value.len());

    let verifiers = "
    component verifier[{{total}}];
    ";
    let source = "
    var d{{num}} = {{ meta_0 }};
    var largest_k{{num}} = {{ meta_1 }};
    signal input sumcheckProof{{num}}[d{{num}} - 1][2 * largest_k{{num}}][{{ meta_4 }}];
    signal input sumcheckr{{num}}[d{{num}} - 1][2 * largest_k{{num}}];
    signal input sumcheckDeltas{{num}}[d{{num}} - 1][2 * largest_k{{num}}];
    signal input sumcheckErrorSigns{{num}}[d{{num}} - 1][2 * largest_k{{num}}];
    signal input q{{num}}[d{{num}} - 1][{{meta_5}}];
    {% if has_d %}
    signal input D{{num}}[{{meta_3}}][{{meta_2}} + 1];
    {% endif %}
    signal input z{{num}}[d{{num}}][largest_k{{num}}];
    signal input r{{num}}[d{{num}} - 1];
    signal input inputFunc{{num}}[{{meta_6}}][{{meta_7}} + 1];
    verifier[{{num}}] = VerifyGKR({{ meta }});
    var a{{num}} = {{ meta_0 }} - 1;
    for (var i = 0; i < a{{num}}; i++) {
        for (var j = 0; j < 2 * {{ meta_1 }}; j++) {
            for (var k = 0; k < {{ meta_4 }}; k++) {
                verifier[{{num}}].sumcheckProof[i][j][k] <== sumcheckProof{{num}}[i][j][k];
            }
        }
    }
    for (var i = 0; i < a{{num}}; i++) {
        for (var j = 0; j < 2 * {{ meta_1 }}; j++) {
            verifier[{{num}}].sumcheckr[i][j] <== sumcheckr{{num}}[i][j];
        }
    }
    for (var i = 0; i < a{{num}}; i++) {
        for (var j = 0; j < 2 * {{ meta_1 }}; j++) {
            verifier[{{num}}].sumcheckDeltas[i][j] <== sumcheckDeltas{{num}}[i][j];
            verifier[{{num}}].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns{{num}}[i][j];
        }
    }
    for (var i = 0; i < a{{num}}; i++) {
        for (var j = 0; j < {{ meta_5 }}; j++) {
            verifier[{{num}}].q[i][j] <== q{{num}}[i][j];
        }
    }
    {% if has_d %}
    for (var i = 0; i < {{ meta_3 }}; i++) {
        for (var j = 0; j < {{ meta_2 }} + 1; j++) {
            verifier[{{num}}].D[i][j] <== D{{num}}[i][j];
        }
    }
    {% endif %}
    for (var i = 0; i < a{{num}} + 1; i++) {
        for (var j = 0; j < {{ meta_1 }}; j++) {
            verifier[{{num}}].z[i][j] <== z{{num}}[i][j];
        }
    }
    for (var i = 0; i < a{{num}}; i++) {
        verifier[{{num}}].r[i] <== r{{num}}[i];
    }
    for (var i = 0; i < {{ meta_6 }}; i++) {
        for (var j = 0; j < {{ meta_7 }} + 1; j++) {
            verifier[{{num}}].inputFunc[i][j] <== inputFunc{{num}}[i][j];
        }
    }
    ";
    added.add_raw_template("verifier", source).unwrap();
    added.add_raw_template("component", verifiers).unwrap();
    let mut decl_ctxt = Context::new();
    decl_ctxt.insert("total", &total);

    let mut v = added.render("component", &decl_ctxt).unwrap();
    for (i, m) in meta_value.iter().enumerate() {
        let mut ctxt = Context::new();
        let meta = format!("{:?}", m.0);
        ctxt.insert("meta", &meta);
        let num = format!("{}", i);
        ctxt.insert("num", &num);
        for (i, value) in m.0.iter().enumerate() {
            let value_string = value.to_string();
            let name = format!("{}_{}", "meta", i.to_string().as_str());

            ctxt.insert(name, &value_string);
        }
        // Add a flag indicating whether meta_3 > 0
        let has_d = m.0.get(3).map(|&v| v > 0).unwrap_or(false);
        ctxt.insert("has_d", &has_d);
        let s = added.render("verifier", &ctxt).unwrap();
        v = format!("{}\n{}", v, s);
    }

    let mut new_circuit = String::new();
    let mut f = File::open(path).expect("original circuit");
    let mut f_content = String::new();
    f.read_to_string(&mut f_content).unwrap();

    let mut is_added = false;
    for line in f_content.lines() {
        if line.eq("pragma circom 2.0.0;") {
            let import =
                String::from("include \"../gkr-verifier-circuits/circom/circom/verifier.circom\";");
            new_circuit = format!("{}\n{}\n", line, import);
        } else if line.eq("}") && !is_added {
            new_circuit = format!("{}\n{}\n}}", new_circuit, v);
            is_added = true;
        } else {
            new_circuit = format!("{}{}\n", new_circuit, line);
        }
    }

    let file_path = current_dir().unwrap().join("aggregated.circom");
    std::fs::write(&file_path, new_circuit).expect("Write new circuit failed");
    file_path.into_os_string().into_string().unwrap()
}

pub fn prove_recursively_circom(
    circuit_path: String,
    previous_proofs: Vec<Proof<Fr>>,
    input_path: String,
) -> Vec<Proof<Fr>> {
    prove_recursively_circom_with_delta(circuit_path, previous_proofs, input_path, None)
}

pub fn prove_recursively_circom_with_delta(
    circuit_path: String,
    previous_proofs: Vec<Proof<Fr>>,
    input_path: String,
    max_delta: Option<Fr>,
) -> Vec<Proof<Fr>> {
    let meta = get_meta(&previous_proofs);
    let modified_proof = modify_proof_for_circom(&previous_proofs, &meta);
    let mut p_vec = vec![];
    for proof in modified_proof {
        p_vec.push(CircomInputProof::new_from_proof(proof));
    }

    let input_name = get_name(&input_path);
    let aggregated_input_path = write_aggregated_input(input_path, p_vec);
    let aggregated_circuit_path = modify_circom_file(circuit_path.clone(), &meta);
    println!("{} generated", aggregated_circuit_path);
    let circom_result = execute_circom(aggregated_circuit_path.clone(), &aggregated_input_path);

    let name = circom_result.0;
    let r1cs_name = format!("{}.r1cs", name.clone());
    let sym_name = format!("{}.sym", name.clone());

    let root_path = circom_result.1;
    let sym = format!("{}{}", root_path.clone(), sym_name);
    let r1cs_path = format!("{}{}", root_path.clone(), r1cs_name);
    let r1cs = R1csFile::<32>::read(File::open(r1cs_path).unwrap()).unwrap();

    let wtns_path = current_dir().unwrap().join("witness.wtns");
    println!("Writing new witness..");
    let wtns = WtnsFile::<32>::read(File::open(wtns_path).unwrap()).unwrap();

    let result = convert_r1cs_wtns_gkr(r1cs, wtns, sym);
    println!("Proving starts..");
    let now = Instant::now();
    let circuit_input_pairs: Vec<(&GKRCircuit<Fr>, &Input<Fr>)> =
        result.0.iter().zip(result.1.iter()).collect();
    let proofs: Vec<Proof<Fr>> = circuit_input_pairs
        .par_iter()
        .map(|(circuit, input)| prove_one(circuit, input, max_delta))
        .collect();

    let time = report_elapsed(now);
    println!("{}\n", format!("Proving {}", time).blue().bold());
    let output_name = format!("{}_output.json", &input_name);
    let output_path = format!("{}{}", root_path.clone(), output_name);
    write_output(output_path, result.2);
    proofs
}

fn report_elapsed(now: Instant) -> String {
    format!(
        "{}",
        format!("took {:?} seconds", now.elapsed().as_secs_f32())
    )
}

pub fn prove_groth(circuit_path: String, previous_proofs: Vec<Proof<Fr>>, input_path: String) {
    let meta = get_meta(&previous_proofs);
    let modified_proof = modify_proof_for_circom(&previous_proofs, &meta);
    let mut p_vec = vec![];
    for proof in modified_proof {
        p_vec.push(CircomInputProof::new_from_proof(proof));
    }
    let aggregated_input_path = write_aggregated_input(input_path, p_vec);
    let aggregated_circuit_path = modify_circom_file(circuit_path, &meta);
    let circom_result = execute_circom(aggregated_circuit_path.clone(), &aggregated_input_path);
    println!("{}", format!("Proving by groth16 can be done").bold());
}

pub fn prove_all(circuit_path: String, input_paths: Vec<String>) {
    prove_all_with_delta(circuit_path, input_paths, None)
}

pub fn prove_all_approx(circuit_path: String, input_paths: Vec<String>, max_delta: Fr) {
    prove_all_with_delta(circuit_path, input_paths, Some(max_delta))
}

fn prove_all_with_delta(circuit_path: String, input_paths: Vec<String>, max_delta: Option<Fr>) {
    // circom circuit --r1cs --sym --c
    // https://docs.circom.io/getting-started/computing-the-witness/#the-witness-file
    let mut proofs = None;
    for (i, input) in input_paths.iter().enumerate() {
        if i == 0 {
            let circom_result = execute_circom(circuit_path.clone(), input);
            let name = circom_result.0;
            let root_path = circom_result.1;

            let input_name = get_name(input);

            let r1cs_name = format!("{}.r1cs", name.clone());
            let r1cs_path = format!("{}{}", root_path.clone(), r1cs_name);
            let r1cs = R1csFile::<32>::read(File::open(r1cs_path).unwrap()).unwrap();
            let sym_name = format!("{}.sym", name.clone());

            let wtns_path = current_dir().unwrap().join("witness.wtns");
            println!("Writing new witness..");
            let wtns = WtnsFile::<32>::read(File::open(wtns_path).unwrap()).unwrap();

            let sym = format!("{}{}", root_path.clone(), sym_name);

            let result = convert_r1cs_wtns_gkr(r1cs, wtns, sym);
            println!("Proving starts..");
            let now = Instant::now();
            let circuit_input_pairs: Vec<(&GKRCircuit<Fr>, &Input<Fr>)> =
                result.0.iter().zip(result.1.iter()).collect();
            let new_proofs: Vec<Proof<Fr>> = circuit_input_pairs
                .par_iter()
                .map(|(circuit, input)| prove_one(circuit, input, max_delta))
                .collect();

            let time = report_elapsed(now);
            println!("{}\n", format!("Proving {}", time).blue().bold());
            proofs = Some(new_proofs);
            let output_name = format!("{}_output.json", &input_name);
            let output_path = format!("{}{}", root_path.clone(), output_name);

            write_output(output_path, result.2);
        } else if i == input_paths.len() - 1 {
            prove_groth(circuit_path.clone(), proofs.clone().unwrap(), input.clone());
        } else {
            proofs = Some(prove_recursively_circom_with_delta(
                circuit_path.clone(),
                proofs.clone().unwrap(),
                input.clone(),
                max_delta,
            ));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::prove_all;
    use std::process::Command;

    fn circom_available() -> bool {
        Command::new("circom").arg("--version").output().is_ok()
    }

    #[test]
    fn test_proving() {
        if !circom_available() {
            eprintln!("circom not found in PATH; skipping test_proving");
            return;
        }
        let circuit_path = String::from("./t.circom");
        let mut input_paths = vec![];
        input_paths.push(String::from("./example/input1.json"));
        input_paths.push(String::from("./example/input2.json"));
        input_paths.push(String::from("./example/input3.json"));
        prove_all(circuit_path, input_paths);
    }

    #[test]
    fn test_single_proof() {
        if !circom_available() {
            eprintln!("circom not found in PATH; skipping test_single_proof");
            return;
        }
        let circuit_path = String::from("./t.circom");
        let mut input_paths = vec![];
        input_paths.push(String::from("./example/input1.json"));
        prove_all(circuit_path, input_paths);
    }
}
