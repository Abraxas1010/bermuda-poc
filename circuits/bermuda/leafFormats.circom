pragma circom 2.1.0;

include "../lib/poseidon.circom";

// Must match:
// - BermudaLicenseRegistry.computeLicenseLeaf
// - BermudaKYCRegistry.computeKycLeaf
// - BermudaNoteRegistry.computeNoteCommitment

template LicenseLeaf() {
    signal input operatorAddress;
    signal input credentialId;
    signal input licenseClass;
    signal input secret;
    signal output leaf;

    // h1 = Poseidon(operator, credentialId)
    component h1 = Poseidon(2);
    h1.inputs[0] <== operatorAddress;
    h1.inputs[1] <== credentialId;

    // h2 = Poseidon(licenseClass, secret)
    component h2 = Poseidon(2);
    h2.inputs[0] <== licenseClass;
    h2.inputs[1] <== secret;

    // leaf = Poseidon(h1, h2)
    component h3 = Poseidon(2);
    h3.inputs[0] <== h1.out;
    h3.inputs[1] <== h2.out;
    leaf <== h3.out;
}

template KycLeaf() {
    signal input holderAddress;
    signal input credentialId;
    signal input kycLevel;
    signal input secret;
    signal output leaf;

    component h1 = Poseidon(2);
    h1.inputs[0] <== holderAddress;
    h1.inputs[1] <== credentialId;

    component h2 = Poseidon(2);
    h2.inputs[0] <== kycLevel;
    h2.inputs[1] <== secret;

    component h3 = Poseidon(2);
    h3.inputs[0] <== h1.out;
    h3.inputs[1] <== h2.out;
    leaf <== h3.out;
}

template NoteCommitment() {
    signal input noteSecret;
    signal input noteSalt;
    signal input amount;
    signal output commitment;

    // h1 = Poseidon(noteSecret, noteSalt)
    component h1 = Poseidon(2);
    h1.inputs[0] <== noteSecret;
    h1.inputs[1] <== noteSalt;

    // commitment = Poseidon(h1, amount)
    component h2 = Poseidon(2);
    h2.inputs[0] <== h1.out;
    h2.inputs[1] <== amount;
    commitment <== h2.out;
}

template NoteNullifier() {
    signal input noteSecret;
    signal input noteSalt;
    signal output nullifier;

    component h = Poseidon(2);
    h.inputs[0] <== noteSecret;
    h.inputs[1] <== noteSalt;
    nullifier <== h.out;
}

