pragma circom 2.1.0;

include "circomlib/circuits/bitify.circom";
include "circomlib/circuits/comparators.circom";

// KYC levels (v0):
// 0 = basic
// 1 = enhanced
// 2 = institutional
//
// Limits (USD cents):
// 0 -> 100000
// 1 -> 1000000
// 2 -> 2^64 (effectively unlimited for 64-bit amounts)

template KycLimitCheck(nBits) {
    signal input kycLevel;
    signal input amount;
    signal output ok;

    // Constrain kycLevel to {0,1,2}
    component lvlBits = Num2Bits(2);
    lvlBits.in <== kycLevel;
    signal b0;
    signal b1;
    b0 <== lvlBits.out[0];
    b1 <== lvlBits.out[1];

    // Disallow 3 (b0=b1=1)
    b0 * b1 === 0;

    // Compute limit via a small selector polynomial.
    var limit0 = 100000;
    var limit1 = 1000000;
    // Institutional is “effectively unlimited” for 64-bit amounts.
    // Use an explicit constant to avoid any compiler-dependent shift semantics.
    var limit2 = 18446744073709551615; // 2^64 - 1

    signal s0;
    signal s1;
    signal s2;
    s0 <== (1 - b0) * (1 - b1);
    s1 <== b0 * (1 - b1);
    s2 <== (1 - b0) * b1;

    signal limit;
    limit <== limit0 * s0 + limit1 * s1 + limit2 * s2;

    component le = LessEqThan(nBits);
    le.in[0] <== amount;
    le.in[1] <== limit;
    ok <== le.out;

    // Enforce success (caller may choose to make this optional later).
    ok === 1;
}
