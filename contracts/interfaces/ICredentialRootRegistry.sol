// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Minimal interface for a Merkle-root registry.
interface ICredentialRootRegistry {
    function isKnownRoot(uint256 root) external view returns (bool);
    function getMerkleRoot() external view returns (uint256);
}
