pragma circom 2.1.0;

include "./bermuda/leafFormats.circom";
include "circomlib/circuits/bitify.circom";

// Prove that a public commitment binds (noteSecret, noteSalt, amount).
// Intended for wiring into the Solidity `deposit` later.
template BermudaNoteDeposit(amountBits) {
    // private
    signal input noteSecret;
    signal input noteSalt;

    // public
    signal input amount;
    signal input commitment;

    // Range-check amount to reduce weird-field-element corner cases.
    component aBits = Num2Bits(amountBits);
    aBits.in <== amount;

    component c = NoteCommitment();
    c.noteSecret <== noteSecret;
    c.noteSalt <== noteSalt;
    c.amount <== amount;
    c.commitment === commitment;
}

component main { public [amount, commitment] } = BermudaNoteDeposit(64);

