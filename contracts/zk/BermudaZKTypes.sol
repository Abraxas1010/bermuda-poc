// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice A Groth16 proof.
struct Groth16Proof {
    uint256[2] a;
    uint256[2][2] b;
    uint256[2] c;
}

/// @notice Public inputs for Bermuda withdraw compliance.
/// @dev Must match `apps/bermuda-poc/circuits/bermudaWithdrawCompliance.circom`.
struct BermudaWithdrawInputs {
    uint256 licenseRoot;
    uint256 kycRoot;
    uint256 noteRoot;
    uint256 nullifier;
    uint256 recipient; // uint160(recipient)
    uint256 amount;
}

/// @notice Public inputs for Bermuda deposit binding.
/// @dev Must match `apps/bermuda-poc/circuits/bermudaNoteDeposit.circom`.
struct BermudaDepositInputs {
    uint256 amount;
    uint256 commitment;
}

interface IBermudaWithdrawVerifier {
    function verifyWithdraw(Groth16Proof calldata proof, BermudaWithdrawInputs calldata inputs)
        external
        view
        returns (bool);
}

interface IBermudaDepositVerifier {
    function verifyDeposit(Groth16Proof calldata proof, BermudaDepositInputs calldata inputs)
        external
        view
        returns (bool);
}

