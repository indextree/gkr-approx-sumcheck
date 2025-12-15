pragma circom 2.0.4;

// =============================================================================
// IEEE 754 Floating Point Circuits for GKR with Approximate Sum-Check
//
// Based on "Sum-Check Protocol for Approximate Computations" (2025)
//
// IEEE 754 Single Precision (32-bit):
// - 1 bit sign (s)
// - 8 bits exponent (e), biased by 127
// - 23 bits mantissa (m), with implicit leading 1
//
// Value = (-1)^s * 2^(e-127) * (1.m)
// =============================================================================

include "../poly/univariate.circom";

// =============================================================================
// Bit Manipulation Helpers
// =============================================================================

// Convert bits to number
template Bits2Num(n) {
    signal input bits[n];
    signal output num;
    
    signal partial[n + 1];
    partial[0] <== 0;
    
    for (var i = 0; i < n; i++) {
        partial[i + 1] <== partial[i] * 2 + bits[i];
    }
    
    num <== partial[n];
}

// Convert number to bits
template Num2Bits(n) {
    signal input num;
    signal output bits[n];
    
    var sum = 0;
    for (var i = 0; i < n; i++) {
        bits[n - 1 - i] <-- (num >> i) & 1;
        bits[n - 1 - i] * (1 - bits[n - 1 - i]) === 0; // Ensure binary
        sum += bits[n - 1 - i] * (1 << i);
    }
    sum === num;
}

// =============================================================================
// IEEE 754 Float Representation
// =============================================================================

// Decompose a 32-bit IEEE 754 float into components
template IEEE754Decompose() {
    signal input bits[32];
    
    signal output sign;
    signal output exponent;
    signal output mantissa;
    
    // Sign bit (bit 31)
    sign <== bits[0];
    
    // Exponent (bits 30-23)
    component expBits = Bits2Num(8);
    for (var i = 0; i < 8; i++) {
        expBits.bits[i] <== bits[1 + i];
    }
    exponent <== expBits.num;
    
    // Mantissa (bits 22-0)
    component mantBits = Bits2Num(23);
    for (var i = 0; i < 23; i++) {
        mantBits.bits[i] <== bits[9 + i];
    }
    mantissa <== mantBits.num;
}

// Compose IEEE 754 float from components
template IEEE754Compose() {
    signal input sign;
    signal input exponent;
    signal input mantissa;
    
    signal output bits[32];
    
    // Sign bit
    bits[0] <== sign;
    
    // Exponent bits
    component expBits = Num2Bits(8);
    expBits.num <== exponent;
    for (var i = 0; i < 8; i++) {
        bits[1 + i] <== expBits.bits[i];
    }
    
    // Mantissa bits
    component mantBits = Num2Bits(23);
    mantBits.num <== mantissa;
    for (var i = 0; i < 23; i++) {
        bits[9 + i] <== mantBits.bits[i];
    }
}

// =============================================================================
// Floating Point Comparison with Epsilon Tolerance
// =============================================================================

// Check if |a - b| <= epsilon (approximate equality)
template FPApproxEqual(mantissaBits) {
    signal input a_sign;
    signal input a_exp;
    signal input a_mant;
    
    signal input b_sign;
    signal input b_exp;
    signal input b_mant;
    
    signal input epsilon;  // Error tolerance
    signal input errorSign; // Hint: 1 if error is "negative" in field
    
    signal output isEqual;
    
    // Compute scaled values (simplified - assumes same exponent for small errors)
    // In practice, we'd need full FP subtraction
    
    // For demonstration, we compare mantissas when exponents match
    signal expMatch;
    expMatch <== (a_exp - b_exp) * (a_exp - b_exp); // 0 if equal
    
    // Compute mantissa difference
    signal mantDiff;
    mantDiff <== a_mant - b_mant;
    
    // Absolute value using hint
    signal absDiff;
    absDiff <== mantDiff * (1 - 2 * errorSign);
    errorSign * (1 - errorSign) === 0;
    
    // Check if within epsilon
    signal slack;
    slack <== epsilon - absDiff;
    // In production, add range check that slack >= 0
    
    isEqual <== 1; // Simplified - actual implementation needs range proofs
}

// =============================================================================
// Floating Point Addition Verification
// =============================================================================

// Verify floating point addition: c ≈ a + b within epsilon
template FPAddVerify() {
    signal input a_sign;
    signal input a_exp;
    signal input a_mant;
    
    signal input b_sign;
    signal input b_exp;
    signal input b_mant;
    
    signal input c_sign;
    signal input c_exp;
    signal input c_mant;
    
    signal input epsilon;     // Maximum allowed error (in ULPs)
    signal input errorSign;   // Hint for absolute value computation
    
    signal output isValid;
    
    // The verification checks that c is a valid result of a + b
    // within the specified epsilon tolerance.
    //
    // For exact verification, we would:
    // 1. Align exponents
    // 2. Add/subtract mantissas
    // 3. Normalize result
    // 4. Check rounding
    //
    // For approximate verification, we accept results within epsilon ULPs
    
    // Simplified check - in production, implement full FP addition verification
    // with range proofs for the error bound
    
    isValid <== 1;
}

// =============================================================================
// Floating Point Multiplication Verification
// =============================================================================

// Verify floating point multiplication: c ≈ a * b within epsilon
template FPMulVerify() {
    signal input a_sign;
    signal input a_exp;
    signal input a_mant;
    
    signal input b_sign;
    signal input b_exp;
    signal input b_mant;
    
    signal input c_sign;
    signal input c_exp;
    signal input c_mant;
    
    signal input epsilon;
    signal input errorSign;
    
    signal output isValid;
    
    // Sign verification: c_sign = a_sign XOR b_sign
    signal expectedSign;
    expectedSign <== a_sign + b_sign - 2 * a_sign * b_sign;
    c_sign === expectedSign;
    
    // Exponent verification: c_exp ≈ a_exp + b_exp - bias (127)
    // Allow for normalization adjustment
    signal expSum;
    expSum <== a_exp + b_exp;
    // c_exp should be close to expSum - 127 (with possible +/- 1 for normalization)
    
    // Mantissa verification would require multiplication and truncation
    // This is simplified - full implementation needs range proofs
    
    isValid <== 1;
}

// =============================================================================
// Floating Point GKR Layer Verification
// =============================================================================

// Verify a layer of FP additions using approximate sumcheck
template FPAddLayerVerify(numGates, nTerms) {
    // Input values (as sign, exponent, mantissa triples)
    signal input prev_signs[2 * numGates];
    signal input prev_exps[2 * numGates];
    signal input prev_mants[2 * numGates];
    
    // Output values
    signal input curr_signs[numGates];
    signal input curr_exps[numGates];
    signal input curr_mants[numGates];
    
    // Gate connections: gate i takes inputs connections[i][0] and connections[i][1]
    signal input connections[numGates][2];
    
    // Epsilon tolerance per gate
    signal input epsilons[numGates];
    signal input errorSigns[numGates];
    
    // Sumcheck proof
    signal input sumcheckProof[numGates][nTerms];
    signal input sumcheckR[numGates - 1];
    signal input sumcheckDeltas[numGates];
    
    signal output isValid;
    signal output totalEpsilon;
    
    // Verify each gate
    component gateVerify[numGates];
    signal gateValid[numGates];
    
    for (var i = 0; i < numGates; i++) {
        gateVerify[i] = FPAddVerify();
        
        // Wire up inputs based on connections
        var leftIdx = connections[i][0];
        var rightIdx = connections[i][1];
        
        gateVerify[i].a_sign <== prev_signs[leftIdx];
        gateVerify[i].a_exp <== prev_exps[leftIdx];
        gateVerify[i].a_mant <== prev_mants[leftIdx];
        
        gateVerify[i].b_sign <== prev_signs[rightIdx];
        gateVerify[i].b_exp <== prev_exps[rightIdx];
        gateVerify[i].b_mant <== prev_mants[rightIdx];
        
        gateVerify[i].c_sign <== curr_signs[i];
        gateVerify[i].c_exp <== curr_exps[i];
        gateVerify[i].c_mant <== curr_mants[i];
        
        gateVerify[i].epsilon <== epsilons[i];
        gateVerify[i].errorSign <== errorSigns[i];
        
        gateValid[i] <== gateVerify[i].isValid;
    }
    
    // Compute total epsilon
    signal partialEps[numGates + 1];
    partialEps[0] <== 0;
    for (var i = 0; i < numGates; i++) {
        partialEps[i + 1] <== partialEps[i] + epsilons[i];
    }
    totalEpsilon <== partialEps[numGates];
    
    // All gates must be valid
    signal partialValid[numGates + 1];
    partialValid[0] <== 1;
    for (var i = 0; i < numGates; i++) {
        partialValid[i + 1] <== partialValid[i] * gateValid[i];
    }
    isValid <== partialValid[numGates];
}

// =============================================================================
// Floating Point GKR Verifier with Approximate Sumcheck
// =============================================================================

// Main FP GKR verifier
template FPGKRVerify(depth, maxGatesPerLayer, nTerms) {
    // Input layer values
    signal input inputSigns[maxGatesPerLayer];
    signal input inputExps[maxGatesPerLayer];
    signal input inputMants[maxGatesPerLayer];
    signal input numInputs;
    
    // Output claim
    signal input outputSign;
    signal input outputExp;
    signal input outputMant;
    
    // Per-layer sumcheck proofs
    signal input layerProofs[depth][maxGatesPerLayer][nTerms];
    signal input layerR[depth][maxGatesPerLayer];
    signal input layerDeltas[depth][maxGatesPerLayer];
    signal input layerEpsilons[depth];
    signal input layerErrorSigns[depth][maxGatesPerLayer];
    
    // Total epsilon tolerance
    signal input totalEpsilon;
    
    signal output isValid;
    signal output accumulatedError;
    
    // Track accumulated error across layers
    signal layerErrors[depth + 1];
    layerErrors[0] <== 0;
    
    // For each layer, verify the approximate sumcheck
    // This is simplified - full implementation would verify each layer's gates
    
    for (var i = 0; i < depth; i++) {
        layerErrors[i + 1] <== layerErrors[i] + layerEpsilons[i];
    }
    
    accumulatedError <== layerErrors[depth];
    
    // Check total error is within bounds
    signal errorSlack;
    errorSlack <== totalEpsilon - accumulatedError;
    // In production, add range check that errorSlack >= 0
    
    isValid <== 1;
}

// =============================================================================
// Dot Product Verification with Approximate Sumcheck
// =============================================================================

// Verify dot product: result ≈ sum(a[i] * b[i]) within epsilon
template FPDotProductVerify(n, nTerms) {
    signal input a_signs[n];
    signal input a_exps[n];
    signal input a_mants[n];
    
    signal input b_signs[n];
    signal input b_exps[n];
    signal input b_mants[n];
    
    signal input result_sign;
    signal input result_exp;
    signal input result_mant;
    
    signal input totalEpsilon;
    signal input intermediateValues[n * 3]; // Products before summation
    signal input sumcheckProof[n][nTerms];
    signal input sumcheckR[n - 1];
    signal input errorSigns[n];
    
    signal output isValid;
    signal output accumulatedError;
    
    // 1. Verify multiplications: products[i] ≈ a[i] * b[i]
    component mulVerify[n];
    for (var i = 0; i < n; i++) {
        mulVerify[i] = FPMulVerify();
        mulVerify[i].a_sign <== a_signs[i];
        mulVerify[i].a_exp <== a_exps[i];
        mulVerify[i].a_mant <== a_mants[i];
        mulVerify[i].b_sign <== b_signs[i];
        mulVerify[i].b_exp <== b_exps[i];
        mulVerify[i].b_mant <== b_mants[i];
        mulVerify[i].c_sign <== intermediateValues[i * 3];
        mulVerify[i].c_exp <== intermediateValues[i * 3 + 1];
        mulVerify[i].c_mant <== intermediateValues[i * 3 + 2];
        mulVerify[i].epsilon <== totalEpsilon; // Simplified
        mulVerify[i].errorSign <== errorSigns[i];
    }
    
    // 2. Verify tree reduction sum using approximate sumcheck
    // This would involve multiple rounds of addition verification
    
    accumulatedError <== 0; // Placeholder
    isValid <== 1;
}
