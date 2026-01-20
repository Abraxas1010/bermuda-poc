// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./BermudaMerkleRegistry.sol";
import "../interfaces/INoteRegistry.sol";

/// @notice Merkle registry for shielded note commitments.
/// @dev The pool contract should be authorized as an inserter.
contract BermudaNoteRegistry is BermudaMerkleRegistry, INoteRegistry {
    mapping(address => bool) public authorizedInserters;

    event InserterAuthorized(address indexed inserter, bool allowed);

    error NotAuthorized();

    modifier onlyInserter() {
        if (!authorizedInserters[msg.sender]) revert NotAuthorized();
        _;
    }

    constructor(address poseidonT2Address) BermudaMerkleRegistry(poseidonT2Address) {}

    /// @notice Standardized note commitment format.
    /// @dev Commitment = Poseidon(Poseidon(noteSecret, noteSalt), amount).
    function computeNoteCommitment(uint256 noteSecret, uint256 noteSalt, uint256 amount)
        public
        view
        returns (uint256)
    {
        uint256[2] memory a = [noteSecret, noteSalt];
        uint256 h1 = poseidonT2.poseidon(a);
        uint256[2] memory b = [h1, amount];
        return poseidonT2.poseidon(b);
    }

    function authorizeInserter(address inserter, bool allowed) external onlyOwner {
        if (inserter == address(0)) revert ZeroAddress();
        authorizedInserters[inserter] = allowed;
        emit InserterAuthorized(inserter, allowed);
    }

    function addLeaf(uint256 leaf)
        external
        override(BermudaMerkleRegistry, INoteRegistry)
        onlyInserter
        returns (uint256 leafIndex)
    {
        leafIndex = _insert(leaf);
        emit LeafAdded(leafIndex, leaf, merkleRoot);
    }
}
