// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./BermudaZKTypes.sol";
import "./GeneratedWithdrawVerifier.sol";

/// @notice Adapter from typed structs to the snarkjs-exported withdraw verifier.
contract BermudaWithdrawVerifier is IBermudaWithdrawVerifier {
    BermudaWithdrawGroth16Verifier public immutable verifier;

    constructor() {
        verifier = new BermudaWithdrawGroth16Verifier();
    }

    function verifyWithdraw(Groth16Proof calldata proof, BermudaWithdrawInputs calldata inputs)
        external
        view
        returns (bool)
    {
        uint256[6] memory pub;
        pub[0] = inputs.licenseRoot;
        pub[1] = inputs.kycRoot;
        pub[2] = inputs.noteRoot;
        pub[3] = inputs.nullifier;
        pub[4] = inputs.recipient;
        pub[5] = inputs.amount;

        return verifier.verifyProof(proof.a, proof.b, proof.c, pub);
    }
}

