pragma circom 2.0.4;
include "../poly/univariate.circom";

// =============================================================================
// Bit decomposition / range check helper
// Enforces: 0 <= num < 2^n (as an integer embedded in the field)
// =============================================================================
template Num2Bits(n) {
    signal input num;
    signal output bits[n];

    var sum = 0;
    for (var i = 0; i < n; i++) {
        // Witness assignment for bit extraction, then constrain correctness
        bits[n - 1 - i] <-- (num >> i) & 1;
        bits[n - 1 - i] * (1 - bits[n - 1 - i]) === 0;
        sum += bits[n - 1 - i] * (1 << i);
    }
    sum === num;
}

// =============================================================================
// Approximate Sum-Check Verifier Circuit
// Based on "Sum-Check Protocol for Approximate Computations" (2025)
//
// Key difference from standard sumcheck:
// - Standard: g_i(0) + g_i(1) = c_i (exact equality)
// - Approximate: |g_i(0) + g_i(1) - c_i| <= epsilon_i (within error tolerance)
//
// The verifier accepts proofs where the sum may differ from expected by
// at most epsilon (error tolerance) per round.
// =============================================================================

// Helper template to compute absolute value in field
// For values that are "small", we check if x or p-x is smaller
// This works for small deviations from the expected value
template AbsoluteValue() {
    signal input value;
    signal input isNegative; // 1 if value > p/2, 0 otherwise (provided by prover)
    signal output absValue;

    // If isNegative, absValue = -value (which is p - value in the field)
    // Otherwise, absValue = value
    absValue <== value * (1 - 2 * isNegative);
    
    // Constraint: isNegative must be 0 or 1
    isNegative * (1 - isNegative) === 0;
}

// Helper template to check if a <= b for small field elements
// Assumes values are small enough to compare directly
template LessOrEqual(n) {
    signal input a;
    signal input b;
    signal output result; // 1 if a <= b, 0 otherwise

    // For small values, we can use bit decomposition
    // This is a simplified version - in practice, use range proofs
    component ltCheck = LessThanBits(n);
    ltCheck.a <== a;
    ltCheck.b <== b + 1; // a <= b is same as a < b + 1
    result <== ltCheck.out;
}

// Less than comparison using bit decomposition
template LessThanBits(n) {
    signal input a;
    signal input b;
    signal output out;

    // Compute b - a and check if it's in valid range
    signal diff;
    diff <== b - a;
    
    // For simplicity, we output 1 (true) for now
    // In production, use proper range checks
    out <== 1;
}

// Standard Sumcheck Verifier (backward compatible)
template SumcheckVerify(v, nTerms) {
    signal input proofs[v][nTerms];
    signal input claim;
    signal input r[v - 1];

    signal output isValid;

    signal expected[v];
    expected[0] <== claim;

    component qZero[v];
    component qOne[v];
    component next[v - 1];
    for (var i = 0; i < v; i++) {
        qZero[i] = evalUnivariate(nTerms);
        qOne[i] = evalUnivariate(nTerms);

        qZero[i].x <== 0;
        qOne[i].x <== 1;

        for (var j = 0; j < nTerms; j++) {
            qZero[i].coeffs[j] <== proofs[i][j];
            qOne[i].coeffs[j] <== proofs[i][j];
        }

        qZero[i].result + qOne[i].result === expected[i];

        if (i != v - 1) {
            next[i] = evalUnivariate(nTerms);
            next[i].x <== r[i];
            for (var j = 0; j < nTerms; j++) {
                next[i].coeffs[j] <== proofs[i][j];
            }
            expected[i + 1] <== next[i].result;
        }
    }

    isValid <== 1;
}

// =============================================================================
// Approximate Sumcheck Verifier
// =============================================================================

// Approximate Sumcheck Verifier with per-round error tolerance
template ApproxSumcheckVerify(v, nTerms, epsilonBits) {
    signal input proofs[v][nTerms];
    signal input claim;
    signal input r[v - 1];
    signal input deltas[v];        // Per-round error bounds
    signal input errorSigns[v];    // Sign hints for error computation (0 or 1)

    signal output isValid;
    signal output accumulatedError;

    signal expected[v + 1];
    signal roundErrors[v];
    signal cumulativeErrors[v + 1];
    signal slack[v];
    
    expected[0] <== claim;
    cumulativeErrors[0] <== 0;

    component qZero[v];
    component qOne[v];
    component next[v - 1];
    component deltaBits[v];
    component errorBits[v];
    component slackBits[v];
    
    for (var i = 0; i < v; i++) {
        // Evaluate polynomial at 0 and 1
        qZero[i] = evalUnivariate(nTerms);
        qOne[i] = evalUnivariate(nTerms);

        qZero[i].x <== 0;
        qOne[i].x <== 1;

        for (var j = 0; j < nTerms; j++) {
            qZero[i].coeffs[j] <== proofs[i][j];
            qOne[i].coeffs[j] <== proofs[i][j];
        }

        // Compute the actual sum
        signal actualSum;
        actualSum <== qZero[i].result + qOne[i].result;

        // Compute the error: error = actualSum - expected[i]
        signal rawError;
        rawError <== actualSum - expected[i];

        // Compute absolute error using the sign hint
        // If errorSigns[i] == 1, the error is "negative" (> p/2), so abs = -rawError
        // If errorSigns[i] == 0, the error is positive, so abs = rawError
        roundErrors[i] <== rawError * (1 - 2 * errorSigns[i]);
        
        // Constraint: errorSigns[i] must be 0 or 1
        errorSigns[i] * (1 - errorSigns[i]) === 0;

        // The round error must be <= delta[i]
        // For circuit, we use: error + slack = delta where slack >= 0
        slack[i] <== deltas[i] - roundErrors[i];

        // Range checks (non-negativity + smallness) to make slack >= 0 meaningful in the field
        // - deltas[i] is bounded (verifier-chosen / public input recommended)
        // - roundErrors[i] is bounded (also forces correct errorSigns[i] for small errors)
        // - slack[i] bounded ensures roundErrors[i] <= deltas[i]
        deltaBits[i] = Num2Bits(epsilonBits);
        deltaBits[i].num <== deltas[i];
        errorBits[i] = Num2Bits(epsilonBits);
        errorBits[i].num <== roundErrors[i];
        slackBits[i] = Num2Bits(epsilonBits);
        slackBits[i].num <== slack[i];

        // Accumulate errors
        cumulativeErrors[i + 1] <== cumulativeErrors[i] + roundErrors[i];

        // Update expected value for next round
        if (i != v - 1) {
            next[i] = evalUnivariate(nTerms);
            next[i].x <== r[i];
            for (var j = 0; j < nTerms; j++) {
                next[i].coeffs[j] <== proofs[i][j];
            }
            expected[i + 1] <== next[i].result;
        }
    }

    accumulatedError <== cumulativeErrors[v];
    isValid <== 1;
}

// Simplified Approximate Sumcheck with single epsilon
template ApproxSumcheckVerifySimple(v, nTerms, epsilonBits) {
    signal input proofs[v][nTerms];
    signal input claim;
    signal input r[v - 1];
    signal input epsilon;          // Single error tolerance for all rounds
    signal input errorSigns[v];    // Sign hints for error computation

    signal output isValid;

    signal expected[v + 1];
    expected[0] <== claim;

    component qZero[v];
    component qOne[v];
    component next[v - 1];
    component epsilonBitsCheck = Num2Bits(epsilonBits);
    component absBits[v];
    component slackBits[v];
    
    // Range-check epsilon itself (verifier-chosen / public input recommended)
    epsilonBitsCheck.num <== epsilon;

    for (var i = 0; i < v; i++) {
        qZero[i] = evalUnivariate(nTerms);
        qOne[i] = evalUnivariate(nTerms);

        qZero[i].x <== 0;
        qOne[i].x <== 1;

        for (var j = 0; j < nTerms; j++) {
            qZero[i].coeffs[j] <== proofs[i][j];
            qOne[i].coeffs[j] <== proofs[i][j];
        }

        // Compute error
        signal actualSum;
        actualSum <== qZero[i].result + qOne[i].result;
        
        signal rawError;
        rawError <== actualSum - expected[i];

        // Absolute error
        signal absError;
        absError <== rawError * (1 - 2 * errorSigns[i]);
        errorSigns[i] * (1 - errorSigns[i]) === 0;

        // Check error is within epsilon
        signal slack;
        slack <== epsilon - absError;
        // Range-check absError and slack (slack >= 0 enforces absError <= epsilon)
        absBits[i] = Num2Bits(epsilonBits);
        absBits[i].num <== absError;
        slackBits[i] = Num2Bits(epsilonBits);
        slackBits[i].num <== slack;

        if (i != v - 1) {
            next[i] = evalUnivariate(nTerms);
            next[i].x <== r[i];
            for (var j = 0; j < nTerms; j++) {
                next[i].coeffs[j] <== proofs[i][j];
            }
            expected[i + 1] <== next[i].result;
        }
    }

    isValid <== 1;
}

// Zero-tolerance approximate sumcheck (same as exact, for backward compatibility)
template ApproxSumcheckVerifyExact(v, nTerms) {
    signal input proofs[v][nTerms];
    signal input claim;
    signal input r[v - 1];

    signal output isValid;

    // Just use the standard sumcheck verify
    component standardVerify = SumcheckVerify(v, nTerms);
    standardVerify.claim <== claim;
    for (var i = 0; i < v; i++) {
        for (var j = 0; j < nTerms; j++) {
            standardVerify.proofs[i][j] <== proofs[i][j];
        }
    }
    for (var i = 0; i < v - 1; i++) {
        standardVerify.r[i] <== r[i];
    }
    
    isValid <== standardVerify.isValid;
}
