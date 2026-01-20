pragma circom 2.1.0;

include "./poseidon.circom";
include "./switch.circom";

// Incremental Merkle path checker using Poseidon(2) as the node hash.
template MerkleTreeChecker(levels) {
    signal input leaf;
    signal input root;
    signal input pathElements[levels];
    signal input pathIndices[levels]; // 0 = leaf is left, 1 = leaf is right

    signal output computedRoot;

    signal levelHashes[levels + 1];
    levelHashes[0] <== leaf;

    component sw[levels];
    component h[levels];

    for (var i = 0; i < levels; i++) {
        sw[i] = Switch();
        sw[i].in[0] <== levelHashes[i];
        sw[i].in[1] <== pathElements[i];
        sw[i].s <== pathIndices[i];

        h[i] = Poseidon(2);
        h[i].inputs[0] <== sw[i].out[0];
        h[i].inputs[1] <== sw[i].out[1];

        levelHashes[i + 1] <== h[i].out;
    }

    computedRoot <== levelHashes[levels];
    computedRoot === root;
}

