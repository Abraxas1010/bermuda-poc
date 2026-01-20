// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./BermudaMerkleRegistry.sol";

/// @notice Merkle registry for valid operator license credentials.
contract BermudaLicenseRegistry is BermudaMerkleRegistry {
    constructor(address poseidonT2Address) BermudaMerkleRegistry(poseidonT2Address) {}

    /// @notice Standardized license leaf format.
    /// @dev Leaf = Poseidon(Poseidon(operator, credentialId), Poseidon(licenseClass, secret)).
    function computeLicenseLeaf(address operator, uint256 credentialId, uint256 licenseClass, uint256 secret)
        public
        view
        returns (uint256)
    {
        uint256[2] memory a = [uint256(uint160(operator)), credentialId];
        uint256 h1 = poseidonT2.poseidon(a);
        uint256[2] memory b = [licenseClass, secret];
        uint256 h2 = poseidonT2.poseidon(b);
        uint256[2] memory c = [h1, h2];
        return poseidonT2.poseidon(c);
    }

    /// @notice Convenience: compute and insert a license leaf.
    function addLicense(address operator, uint256 credentialId, uint256 licenseClass, uint256 secret)
        external
        onlyOwner
        returns (uint256 leafIndex)
    {
        uint256 leaf = computeLicenseLeaf(operator, credentialId, licenseClass, secret);
        leafIndex = _insert(leaf);
        emit LeafAdded(leafIndex, leaf, merkleRoot);
    }
}
