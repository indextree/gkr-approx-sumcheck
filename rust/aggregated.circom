pragma circom 2.0.0;
include "../gkr-verifier-circuits/circom/circom/verifier.circom";
include "../gkr-verifier-circuits/circom/node_modules/circomlib/circuits/mimc.circom";

template A(){
    signal input in1;
    signal input in2;
    signal output out;

    component hasher = MiMC7(91);
    hasher.x_in <== in1;
    hasher.k <== 0;
    
    out <== hasher.out;


    component verifier[12];
    

    var d0 = 5;
    var largest_k0 = 7;
    signal input sumcheckProof0[d0 - 1][2 * largest_k0][3];
    signal input sumcheckr0[d0 - 1][2 * largest_k0];
    signal input sumcheckDeltas0[d0 - 1][2 * largest_k0];
    signal input sumcheckErrorSigns0[d0 - 1][2 * largest_k0];
    signal input q0[d0 - 1][8];
    
    signal input D0[1][5 + 1];
    
    signal input z0[d0][largest_k0];
    signal input r0[d0 - 1];
    signal input inputFunc0[63][6 + 1];
    verifier[0] = VerifyGKR([5, 7, 5, 1, 3, 8, 63, 6, 5, 6, 7, 6, 6]);
    var a0 = 5 - 1;
    for (var i = 0; i < a0; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[0].sumcheckProof[i][j][k] <== sumcheckProof0[i][j][k];
            }
        }
    }
    for (var i = 0; i < a0; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[0].sumcheckr[i][j] <== sumcheckr0[i][j];
        }
    }
    for (var i = 0; i < a0; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[0].sumcheckDeltas[i][j] <== sumcheckDeltas0[i][j];
            verifier[0].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns0[i][j];
        }
    }
    for (var i = 0; i < a0; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[0].q[i][j] <== q0[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[0].D[i][j] <== D0[i][j];
        }
    }
    
    for (var i = 0; i < a0 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[0].z[i][j] <== z0[i][j];
        }
    }
    for (var i = 0; i < a0; i++) {
        verifier[0].r[i] <== r0[i];
    }
    for (var i = 0; i < 63; i++) {
        for (var j = 0; j < 6 + 1; j++) {
            verifier[0].inputFunc[i][j] <== inputFunc0[i][j];
        }
    }
    

    var d1 = 5;
    var largest_k1 = 7;
    signal input sumcheckProof1[d1 - 1][2 * largest_k1][3];
    signal input sumcheckr1[d1 - 1][2 * largest_k1];
    signal input sumcheckDeltas1[d1 - 1][2 * largest_k1];
    signal input sumcheckErrorSigns1[d1 - 1][2 * largest_k1];
    signal input q1[d1 - 1][8];
    
    signal input D1[1][5 + 1];
    
    signal input z1[d1][largest_k1];
    signal input r1[d1 - 1];
    signal input inputFunc1[63][6 + 1];
    verifier[1] = VerifyGKR([5, 7, 5, 1, 3, 8, 63, 6, 5, 6, 7, 7, 6]);
    var a1 = 5 - 1;
    for (var i = 0; i < a1; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[1].sumcheckProof[i][j][k] <== sumcheckProof1[i][j][k];
            }
        }
    }
    for (var i = 0; i < a1; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[1].sumcheckr[i][j] <== sumcheckr1[i][j];
        }
    }
    for (var i = 0; i < a1; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[1].sumcheckDeltas[i][j] <== sumcheckDeltas1[i][j];
            verifier[1].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns1[i][j];
        }
    }
    for (var i = 0; i < a1; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[1].q[i][j] <== q1[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[1].D[i][j] <== D1[i][j];
        }
    }
    
    for (var i = 0; i < a1 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[1].z[i][j] <== z1[i][j];
        }
    }
    for (var i = 0; i < a1; i++) {
        verifier[1].r[i] <== r1[i];
    }
    for (var i = 0; i < 63; i++) {
        for (var j = 0; j < 6 + 1; j++) {
            verifier[1].inputFunc[i][j] <== inputFunc1[i][j];
        }
    }
    

    var d2 = 5;
    var largest_k2 = 7;
    signal input sumcheckProof2[d2 - 1][2 * largest_k2][3];
    signal input sumcheckr2[d2 - 1][2 * largest_k2];
    signal input sumcheckDeltas2[d2 - 1][2 * largest_k2];
    signal input sumcheckErrorSigns2[d2 - 1][2 * largest_k2];
    signal input q2[d2 - 1][8];
    
    signal input D2[1][5 + 1];
    
    signal input z2[d2][largest_k2];
    signal input r2[d2 - 1];
    signal input inputFunc2[63][6 + 1];
    verifier[2] = VerifyGKR([5, 7, 5, 1, 3, 8, 63, 6, 5, 6, 7, 7, 6]);
    var a2 = 5 - 1;
    for (var i = 0; i < a2; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[2].sumcheckProof[i][j][k] <== sumcheckProof2[i][j][k];
            }
        }
    }
    for (var i = 0; i < a2; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[2].sumcheckr[i][j] <== sumcheckr2[i][j];
        }
    }
    for (var i = 0; i < a2; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[2].sumcheckDeltas[i][j] <== sumcheckDeltas2[i][j];
            verifier[2].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns2[i][j];
        }
    }
    for (var i = 0; i < a2; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[2].q[i][j] <== q2[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[2].D[i][j] <== D2[i][j];
        }
    }
    
    for (var i = 0; i < a2 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[2].z[i][j] <== z2[i][j];
        }
    }
    for (var i = 0; i < a2; i++) {
        verifier[2].r[i] <== r2[i];
    }
    for (var i = 0; i < 63; i++) {
        for (var j = 0; j < 6 + 1; j++) {
            verifier[2].inputFunc[i][j] <== inputFunc2[i][j];
        }
    }
    

    var d3 = 5;
    var largest_k3 = 7;
    signal input sumcheckProof3[d3 - 1][2 * largest_k3][3];
    signal input sumcheckr3[d3 - 1][2 * largest_k3];
    signal input sumcheckDeltas3[d3 - 1][2 * largest_k3];
    signal input sumcheckErrorSigns3[d3 - 1][2 * largest_k3];
    signal input q3[d3 - 1][8];
    
    signal input D3[1][5 + 1];
    
    signal input z3[d3][largest_k3];
    signal input r3[d3 - 1];
    signal input inputFunc3[63][6 + 1];
    verifier[3] = VerifyGKR([5, 7, 5, 1, 3, 8, 63, 6, 5, 6, 7, 7, 6]);
    var a3 = 5 - 1;
    for (var i = 0; i < a3; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[3].sumcheckProof[i][j][k] <== sumcheckProof3[i][j][k];
            }
        }
    }
    for (var i = 0; i < a3; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[3].sumcheckr[i][j] <== sumcheckr3[i][j];
        }
    }
    for (var i = 0; i < a3; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[3].sumcheckDeltas[i][j] <== sumcheckDeltas3[i][j];
            verifier[3].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns3[i][j];
        }
    }
    for (var i = 0; i < a3; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[3].q[i][j] <== q3[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[3].D[i][j] <== D3[i][j];
        }
    }
    
    for (var i = 0; i < a3 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[3].z[i][j] <== z3[i][j];
        }
    }
    for (var i = 0; i < a3; i++) {
        verifier[3].r[i] <== r3[i];
    }
    for (var i = 0; i < 63; i++) {
        for (var j = 0; j < 6 + 1; j++) {
            verifier[3].inputFunc[i][j] <== inputFunc3[i][j];
        }
    }
    

    var d4 = 5;
    var largest_k4 = 7;
    signal input sumcheckProof4[d4 - 1][2 * largest_k4][3];
    signal input sumcheckr4[d4 - 1][2 * largest_k4];
    signal input sumcheckDeltas4[d4 - 1][2 * largest_k4];
    signal input sumcheckErrorSigns4[d4 - 1][2 * largest_k4];
    signal input q4[d4 - 1][8];
    
    signal input D4[1][5 + 1];
    
    signal input z4[d4][largest_k4];
    signal input r4[d4 - 1];
    signal input inputFunc4[63][6 + 1];
    verifier[4] = VerifyGKR([5, 7, 5, 1, 3, 8, 63, 6, 5, 6, 7, 7, 6]);
    var a4 = 5 - 1;
    for (var i = 0; i < a4; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[4].sumcheckProof[i][j][k] <== sumcheckProof4[i][j][k];
            }
        }
    }
    for (var i = 0; i < a4; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[4].sumcheckr[i][j] <== sumcheckr4[i][j];
        }
    }
    for (var i = 0; i < a4; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[4].sumcheckDeltas[i][j] <== sumcheckDeltas4[i][j];
            verifier[4].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns4[i][j];
        }
    }
    for (var i = 0; i < a4; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[4].q[i][j] <== q4[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[4].D[i][j] <== D4[i][j];
        }
    }
    
    for (var i = 0; i < a4 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[4].z[i][j] <== z4[i][j];
        }
    }
    for (var i = 0; i < a4; i++) {
        verifier[4].r[i] <== r4[i];
    }
    for (var i = 0; i < 63; i++) {
        for (var j = 0; j < 6 + 1; j++) {
            verifier[4].inputFunc[i][j] <== inputFunc4[i][j];
        }
    }
    

    var d5 = 6;
    var largest_k5 = 7;
    signal input sumcheckProof5[d5 - 1][2 * largest_k5][3];
    signal input sumcheckr5[d5 - 1][2 * largest_k5];
    signal input sumcheckDeltas5[d5 - 1][2 * largest_k5];
    signal input sumcheckErrorSigns5[d5 - 1][2 * largest_k5];
    signal input q5[d5 - 1][8];
    
    signal input D5[1][5 + 1];
    
    signal input z5[d5][largest_k5];
    signal input r5[d5 - 1];
    signal input inputFunc5[63][6 + 1];
    verifier[5] = VerifyGKR([6, 7, 5, 1, 3, 8, 63, 6, 5, 6, 7, 7, 6, 6]);
    var a5 = 6 - 1;
    for (var i = 0; i < a5; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[5].sumcheckProof[i][j][k] <== sumcheckProof5[i][j][k];
            }
        }
    }
    for (var i = 0; i < a5; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[5].sumcheckr[i][j] <== sumcheckr5[i][j];
        }
    }
    for (var i = 0; i < a5; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[5].sumcheckDeltas[i][j] <== sumcheckDeltas5[i][j];
            verifier[5].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns5[i][j];
        }
    }
    for (var i = 0; i < a5; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[5].q[i][j] <== q5[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[5].D[i][j] <== D5[i][j];
        }
    }
    
    for (var i = 0; i < a5 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[5].z[i][j] <== z5[i][j];
        }
    }
    for (var i = 0; i < a5; i++) {
        verifier[5].r[i] <== r5[i];
    }
    for (var i = 0; i < 63; i++) {
        for (var j = 0; j < 6 + 1; j++) {
            verifier[5].inputFunc[i][j] <== inputFunc5[i][j];
        }
    }
    

    var d6 = 6;
    var largest_k6 = 7;
    signal input sumcheckProof6[d6 - 1][2 * largest_k6][3];
    signal input sumcheckr6[d6 - 1][2 * largest_k6];
    signal input sumcheckDeltas6[d6 - 1][2 * largest_k6];
    signal input sumcheckErrorSigns6[d6 - 1][2 * largest_k6];
    signal input q6[d6 - 1][8];
    
    signal input D6[1][5 + 1];
    
    signal input z6[d6][largest_k6];
    signal input r6[d6 - 1];
    signal input inputFunc6[127][7 + 1];
    verifier[6] = VerifyGKR([6, 7, 5, 1, 3, 8, 127, 7, 5, 6, 7, 7, 7, 7]);
    var a6 = 6 - 1;
    for (var i = 0; i < a6; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[6].sumcheckProof[i][j][k] <== sumcheckProof6[i][j][k];
            }
        }
    }
    for (var i = 0; i < a6; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[6].sumcheckr[i][j] <== sumcheckr6[i][j];
        }
    }
    for (var i = 0; i < a6; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[6].sumcheckDeltas[i][j] <== sumcheckDeltas6[i][j];
            verifier[6].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns6[i][j];
        }
    }
    for (var i = 0; i < a6; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[6].q[i][j] <== q6[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[6].D[i][j] <== D6[i][j];
        }
    }
    
    for (var i = 0; i < a6 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[6].z[i][j] <== z6[i][j];
        }
    }
    for (var i = 0; i < a6; i++) {
        verifier[6].r[i] <== r6[i];
    }
    for (var i = 0; i < 127; i++) {
        for (var j = 0; j < 7 + 1; j++) {
            verifier[6].inputFunc[i][j] <== inputFunc6[i][j];
        }
    }
    

    var d7 = 6;
    var largest_k7 = 7;
    signal input sumcheckProof7[d7 - 1][2 * largest_k7][3];
    signal input sumcheckr7[d7 - 1][2 * largest_k7];
    signal input sumcheckDeltas7[d7 - 1][2 * largest_k7];
    signal input sumcheckErrorSigns7[d7 - 1][2 * largest_k7];
    signal input q7[d7 - 1][8];
    
    signal input D7[1][5 + 1];
    
    signal input z7[d7][largest_k7];
    signal input r7[d7 - 1];
    signal input inputFunc7[127][7 + 1];
    verifier[7] = VerifyGKR([6, 7, 5, 1, 3, 8, 127, 7, 5, 6, 7, 7, 7, 7]);
    var a7 = 6 - 1;
    for (var i = 0; i < a7; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[7].sumcheckProof[i][j][k] <== sumcheckProof7[i][j][k];
            }
        }
    }
    for (var i = 0; i < a7; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[7].sumcheckr[i][j] <== sumcheckr7[i][j];
        }
    }
    for (var i = 0; i < a7; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[7].sumcheckDeltas[i][j] <== sumcheckDeltas7[i][j];
            verifier[7].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns7[i][j];
        }
    }
    for (var i = 0; i < a7; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[7].q[i][j] <== q7[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[7].D[i][j] <== D7[i][j];
        }
    }
    
    for (var i = 0; i < a7 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[7].z[i][j] <== z7[i][j];
        }
    }
    for (var i = 0; i < a7; i++) {
        verifier[7].r[i] <== r7[i];
    }
    for (var i = 0; i < 127; i++) {
        for (var j = 0; j < 7 + 1; j++) {
            verifier[7].inputFunc[i][j] <== inputFunc7[i][j];
        }
    }
    

    var d8 = 6;
    var largest_k8 = 7;
    signal input sumcheckProof8[d8 - 1][2 * largest_k8][3];
    signal input sumcheckr8[d8 - 1][2 * largest_k8];
    signal input sumcheckDeltas8[d8 - 1][2 * largest_k8];
    signal input sumcheckErrorSigns8[d8 - 1][2 * largest_k8];
    signal input q8[d8 - 1][8];
    
    signal input D8[1][5 + 1];
    
    signal input z8[d8][largest_k8];
    signal input r8[d8 - 1];
    signal input inputFunc8[127][7 + 1];
    verifier[8] = VerifyGKR([6, 7, 5, 1, 3, 8, 127, 7, 5, 6, 7, 7, 7, 7]);
    var a8 = 6 - 1;
    for (var i = 0; i < a8; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[8].sumcheckProof[i][j][k] <== sumcheckProof8[i][j][k];
            }
        }
    }
    for (var i = 0; i < a8; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[8].sumcheckr[i][j] <== sumcheckr8[i][j];
        }
    }
    for (var i = 0; i < a8; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[8].sumcheckDeltas[i][j] <== sumcheckDeltas8[i][j];
            verifier[8].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns8[i][j];
        }
    }
    for (var i = 0; i < a8; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[8].q[i][j] <== q8[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[8].D[i][j] <== D8[i][j];
        }
    }
    
    for (var i = 0; i < a8 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[8].z[i][j] <== z8[i][j];
        }
    }
    for (var i = 0; i < a8; i++) {
        verifier[8].r[i] <== r8[i];
    }
    for (var i = 0; i < 127; i++) {
        for (var j = 0; j < 7 + 1; j++) {
            verifier[8].inputFunc[i][j] <== inputFunc8[i][j];
        }
    }
    

    var d9 = 6;
    var largest_k9 = 7;
    signal input sumcheckProof9[d9 - 1][2 * largest_k9][3];
    signal input sumcheckr9[d9 - 1][2 * largest_k9];
    signal input sumcheckDeltas9[d9 - 1][2 * largest_k9];
    signal input sumcheckErrorSigns9[d9 - 1][2 * largest_k9];
    signal input q9[d9 - 1][8];
    
    signal input D9[1][5 + 1];
    
    signal input z9[d9][largest_k9];
    signal input r9[d9 - 1];
    signal input inputFunc9[127][7 + 1];
    verifier[9] = VerifyGKR([6, 7, 5, 1, 3, 8, 127, 7, 5, 6, 7, 7, 7, 7]);
    var a9 = 6 - 1;
    for (var i = 0; i < a9; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[9].sumcheckProof[i][j][k] <== sumcheckProof9[i][j][k];
            }
        }
    }
    for (var i = 0; i < a9; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[9].sumcheckr[i][j] <== sumcheckr9[i][j];
        }
    }
    for (var i = 0; i < a9; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[9].sumcheckDeltas[i][j] <== sumcheckDeltas9[i][j];
            verifier[9].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns9[i][j];
        }
    }
    for (var i = 0; i < a9; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[9].q[i][j] <== q9[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[9].D[i][j] <== D9[i][j];
        }
    }
    
    for (var i = 0; i < a9 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[9].z[i][j] <== z9[i][j];
        }
    }
    for (var i = 0; i < a9; i++) {
        verifier[9].r[i] <== r9[i];
    }
    for (var i = 0; i < 127; i++) {
        for (var j = 0; j < 7 + 1; j++) {
            verifier[9].inputFunc[i][j] <== inputFunc9[i][j];
        }
    }
    

    var d10 = 6;
    var largest_k10 = 7;
    signal input sumcheckProof10[d10 - 1][2 * largest_k10][3];
    signal input sumcheckr10[d10 - 1][2 * largest_k10];
    signal input sumcheckDeltas10[d10 - 1][2 * largest_k10];
    signal input sumcheckErrorSigns10[d10 - 1][2 * largest_k10];
    signal input q10[d10 - 1][8];
    
    signal input D10[1][5 + 1];
    
    signal input z10[d10][largest_k10];
    signal input r10[d10 - 1];
    signal input inputFunc10[127][7 + 1];
    verifier[10] = VerifyGKR([6, 7, 5, 1, 3, 8, 127, 7, 5, 6, 7, 7, 7, 7]);
    var a10 = 6 - 1;
    for (var i = 0; i < a10; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[10].sumcheckProof[i][j][k] <== sumcheckProof10[i][j][k];
            }
        }
    }
    for (var i = 0; i < a10; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[10].sumcheckr[i][j] <== sumcheckr10[i][j];
        }
    }
    for (var i = 0; i < a10; i++) {
        for (var j = 0; j < 2 * 7; j++) {
            verifier[10].sumcheckDeltas[i][j] <== sumcheckDeltas10[i][j];
            verifier[10].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns10[i][j];
        }
    }
    for (var i = 0; i < a10; i++) {
        for (var j = 0; j < 8; j++) {
            verifier[10].q[i][j] <== q10[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 5 + 1; j++) {
            verifier[10].D[i][j] <== D10[i][j];
        }
    }
    
    for (var i = 0; i < a10 + 1; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[10].z[i][j] <== z10[i][j];
        }
    }
    for (var i = 0; i < a10; i++) {
        verifier[10].r[i] <== r10[i];
    }
    for (var i = 0; i < 127; i++) {
        for (var j = 0; j < 7 + 1; j++) {
            verifier[10].inputFunc[i][j] <== inputFunc10[i][j];
        }
    }
    

    var d11 = 6;
    var largest_k11 = 6;
    signal input sumcheckProof11[d11 - 1][2 * largest_k11][3];
    signal input sumcheckr11[d11 - 1][2 * largest_k11];
    signal input sumcheckDeltas11[d11 - 1][2 * largest_k11];
    signal input sumcheckErrorSigns11[d11 - 1][2 * largest_k11];
    signal input q11[d11 - 1][7];
    
    signal input D11[1][4 + 1];
    
    signal input z11[d11][largest_k11];
    signal input r11[d11 - 1];
    signal input inputFunc11[63][6 + 1];
    verifier[11] = VerifyGKR([6, 6, 4, 1, 3, 7, 63, 6, 4, 5, 5, 6, 6, 6]);
    var a11 = 6 - 1;
    for (var i = 0; i < a11; i++) {
        for (var j = 0; j < 2 * 6; j++) {
            for (var k = 0; k < 3; k++) {
                verifier[11].sumcheckProof[i][j][k] <== sumcheckProof11[i][j][k];
            }
        }
    }
    for (var i = 0; i < a11; i++) {
        for (var j = 0; j < 2 * 6; j++) {
            verifier[11].sumcheckr[i][j] <== sumcheckr11[i][j];
        }
    }
    for (var i = 0; i < a11; i++) {
        for (var j = 0; j < 2 * 6; j++) {
            verifier[11].sumcheckDeltas[i][j] <== sumcheckDeltas11[i][j];
            verifier[11].sumcheckErrorSigns[i][j] <== sumcheckErrorSigns11[i][j];
        }
    }
    for (var i = 0; i < a11; i++) {
        for (var j = 0; j < 7; j++) {
            verifier[11].q[i][j] <== q11[i][j];
        }
    }
    
    for (var i = 0; i < 1; i++) {
        for (var j = 0; j < 4 + 1; j++) {
            verifier[11].D[i][j] <== D11[i][j];
        }
    }
    
    for (var i = 0; i < a11 + 1; i++) {
        for (var j = 0; j < 6; j++) {
            verifier[11].z[i][j] <== z11[i][j];
        }
    }
    for (var i = 0; i < a11; i++) {
        verifier[11].r[i] <== r11[i];
    }
    for (var i = 0; i < 63; i++) {
        for (var j = 0; j < 6 + 1; j++) {
            verifier[11].inputFunc[i][j] <== inputFunc11[i][j];
        }
    }
    
}
component main {public [in1]}= A();
