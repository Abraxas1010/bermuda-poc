// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./ICredentialRootRegistry.sol";

/// @notice Note commitment Merkle registry.
interface INoteRegistry is ICredentialRootRegistry {
    function addLeaf(uint256 leaf) external returns (uint256 leafIndex);
}

