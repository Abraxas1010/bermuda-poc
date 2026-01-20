// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./BermudaZKTypes.sol";
import "./GeneratedDepositVerifier.sol";

/// @notice Adapter from typed structs to the snarkjs-exported deposit verifier.
contract BermudaDepositVerifier is IBermudaDepositVerifier {
    BermudaDepositGroth16Verifier public immutable verifier;

    constructor() {
        verifier = new BermudaDepositGroth16Verifier();
    }

    function verifyDeposit(Groth16Proof calldata proof, BermudaDepositInputs calldata inputs)
        external
        view
        returns (bool)
    {
        uint256[2] memory pub;
        pub[0] = inputs.amount;
        pub[1] = inputs.commitment;

        return verifier.verifyProof(proof.a, proof.b, proof.c, pub);
    }
}

