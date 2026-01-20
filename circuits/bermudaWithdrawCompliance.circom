pragma circom 2.1.0;

include "./lib/merkleTree.circom";
include "./bermuda/leafFormats.circom";
include "./bermuda/kycLimit.circom";

// Public inputs layout must match Solidity pool ABI:
//   [licenseRoot, kycRoot, noteRoot, nullifier, recipient(uint160), amount]
template BermudaWithdrawCompliance(treeLevels, amountBits) {
    // === Private witnesses ===

    // Operator license
    signal input operatorAddress;
    signal input operatorCredentialId;
    signal input operatorLicenseClass;
    signal input operatorSecret;
    signal input operatorPathElements[treeLevels];
    signal input operatorPathIndices[treeLevels];

    // Sender KYC
    signal input senderAddress;
    signal input senderCredentialId;
    signal input senderKycLevel;
    signal input senderSecret;
    signal input senderPathElements[treeLevels];
    signal input senderPathIndices[treeLevels];

    // Note
    signal input noteSecret;
    signal input noteSalt;
    signal input notePathElements[treeLevels];
    signal input notePathIndices[treeLevels];

    // === Public inputs ===
    signal input licenseRoot;
    signal input kycRoot;
    signal input noteRoot;
    signal input nullifier;
    signal input recipient;
    signal input amount;

    // 1) Operator license membership
    component opLeaf = LicenseLeaf();
    opLeaf.operatorAddress <== operatorAddress;
    opLeaf.credentialId <== operatorCredentialId;
    opLeaf.licenseClass <== operatorLicenseClass;
    opLeaf.secret <== operatorSecret;

    component opMerkle = MerkleTreeChecker(treeLevels);
    opMerkle.leaf <== opLeaf.leaf;
    opMerkle.root <== licenseRoot;
    for (var i = 0; i < treeLevels; i++) {
        opMerkle.pathElements[i] <== operatorPathElements[i];
        opMerkle.pathIndices[i] <== operatorPathIndices[i];
    }

    // 2) Sender KYC membership
    component kycLeaf = KycLeaf();
    kycLeaf.holderAddress <== senderAddress;
    kycLeaf.credentialId <== senderCredentialId;
    kycLeaf.kycLevel <== senderKycLevel;
    kycLeaf.secret <== senderSecret;

    component kycMerkle = MerkleTreeChecker(treeLevels);
    kycMerkle.leaf <== kycLeaf.leaf;
    kycMerkle.root <== kycRoot;
    for (var j = 0; j < treeLevels; j++) {
        kycMerkle.pathElements[j] <== senderPathElements[j];
        kycMerkle.pathIndices[j] <== senderPathIndices[j];
    }

    // 3) Amount within sender KYC limit
    component limit = KycLimitCheck(amountBits);
    limit.kycLevel <== senderKycLevel;
    limit.amount <== amount;

    // 4) Note membership in noteRoot, binding `amount`
    component noteCommit = NoteCommitment();
    noteCommit.noteSecret <== noteSecret;
    noteCommit.noteSalt <== noteSalt;
    noteCommit.amount <== amount;

    component noteMerkle = MerkleTreeChecker(treeLevels);
    noteMerkle.leaf <== noteCommit.commitment;
    noteMerkle.root <== noteRoot;
    for (var k = 0; k < treeLevels; k++) {
        noteMerkle.pathElements[k] <== notePathElements[k];
        noteMerkle.pathIndices[k] <== notePathIndices[k];
    }

    // 5) Nullifier derived from note secret
    component n = NoteNullifier();
    n.noteSecret <== noteSecret;
    n.noteSalt <== noteSalt;
    n.nullifier === nullifier;
}

component main { public [licenseRoot, kycRoot, noteRoot, nullifier, recipient, amount] } =
    BermudaWithdrawCompliance(20, 64);

