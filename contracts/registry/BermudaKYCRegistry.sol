// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./BermudaMerkleRegistry.sol";

/// @notice Merkle registry for KYC credentials.
contract BermudaKYCRegistry is BermudaMerkleRegistry {
    constructor(address poseidonT2Address) BermudaMerkleRegistry(poseidonT2Address) {}

    /// @notice Standardized KYC leaf format.
    /// @dev Leaf = Poseidon(Poseidon(holder, credentialId), Poseidon(kycLevel, secret)).
    function computeKycLeaf(address holder, uint256 credentialId, uint256 kycLevel, uint256 secret)
        public
        view
        returns (uint256)
    {
        uint256[2] memory a = [uint256(uint160(holder)), credentialId];
        uint256 h1 = poseidonT2.poseidon(a);
        uint256[2] memory b = [kycLevel, secret];
        uint256 h2 = poseidonT2.poseidon(b);
        uint256[2] memory c = [h1, h2];
        return poseidonT2.poseidon(c);
    }

    /// @notice Convenience: compute and insert a KYC leaf.
    function addKycCredential(address holder, uint256 credentialId, uint256 kycLevel, uint256 secret)
        external
        onlyOwner
        returns (uint256 leafIndex)
    {
        uint256 leaf = computeKycLeaf(holder, credentialId, kycLevel, secret);
        leafIndex = _insert(leaf);
        emit LeafAdded(leafIndex, leaf, merkleRoot);
    }
}
