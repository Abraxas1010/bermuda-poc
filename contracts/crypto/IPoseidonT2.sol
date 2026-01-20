// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Minimal Poseidon(2) interface (circomlibjs-compatible deployments).
interface IPoseidonT2 {
    function poseidon(uint256[2] calldata input) external pure returns (uint256);
}

