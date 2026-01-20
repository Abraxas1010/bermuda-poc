// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "../crypto/IPoseidonT2.sol";
import "../interfaces/ICredentialRootRegistry.sol";

/// @title BermudaMerkleRegistry
/// @notice Incremental Merkle tree (Poseidon(2)) with a root history.
/// @dev This is a minimalized variant of the pattern used in `apps/base-contracts/`.
contract BermudaMerkleRegistry is ICredentialRootRegistry {
    uint256 public constant TREE_DEPTH = 20;
    uint256 public constant ROOT_HISTORY_SIZE = 100;

    address public owner;
    IPoseidonT2 public poseidonT2;

    uint256 public merkleRoot;
    uint256 public nextLeafIndex;

    mapping(uint256 => bool) public knownRoots;
    uint256[ROOT_HISTORY_SIZE] public rootHistory;
    uint256 public currentRootIndex;

    uint256[TREE_DEPTH] public zeros;
    uint256[TREE_DEPTH] public filledSubtrees;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);
    event PoseidonSet(address indexed poseidon);
    event LeafAdded(uint256 indexed leafIndex, uint256 leaf, uint256 newRoot);

    error NotOwner();
    error ZeroAddress();
    error TreeFull();
    error TreeNotEmpty();

    modifier onlyOwner() {
        if (msg.sender != owner) revert NotOwner();
        _;
    }

    constructor(address poseidonT2Address) {
        owner = msg.sender;
        emit OwnershipTransferred(address(0), msg.sender);
        _setPoseidon(poseidonT2Address);
    }

    function transferOwnership(address newOwner) external onlyOwner {
        if (newOwner == address(0)) revert ZeroAddress();
        emit OwnershipTransferred(owner, newOwner);
        owner = newOwner;
    }

    function setPoseidon(address poseidonT2Address) external onlyOwner {
        if (nextLeafIndex != 0) revert TreeNotEmpty();
        _setPoseidon(poseidonT2Address);
    }

    function _setPoseidon(address poseidonT2Address) internal {
        if (poseidonT2Address == address(0)) revert ZeroAddress();
        poseidonT2 = IPoseidonT2(poseidonT2Address);
        emit PoseidonSet(poseidonT2Address);

        _initZeros();
        merkleRoot = zeros[TREE_DEPTH - 1];
        _addRoot(merkleRoot);
    }

    function getMerkleRoot() external view returns (uint256) {
        return merkleRoot;
    }

    function isKnownRoot(uint256 root) external view returns (bool) {
        return knownRoots[root];
    }

    function addLeaf(uint256 leaf) external virtual onlyOwner returns (uint256 leafIndex) {
        leafIndex = _insert(leaf);
        emit LeafAdded(leafIndex, leaf, merkleRoot);
    }

    function hashLeftRight(uint256 left, uint256 right) public view returns (uint256) {
        uint256[2] memory input = [left, right];
        return poseidonT2.poseidon(input);
    }

    function _initZeros() internal {
        zeros[0] = hashLeftRight(0, 0);
        for (uint256 i = 1; i < TREE_DEPTH; i++) {
            zeros[i] = hashLeftRight(zeros[i - 1], zeros[i - 1]);
        }
        for (uint256 i = 0; i < TREE_DEPTH; i++) {
            filledSubtrees[i] = zeros[i];
        }
    }

    function _addRoot(uint256 root) internal {
        knownRoots[root] = true;
        rootHistory[currentRootIndex] = root;
        currentRootIndex = (currentRootIndex + 1) % ROOT_HISTORY_SIZE;
        merkleRoot = root;
    }

    function _insert(uint256 leaf) internal returns (uint256 index) {
        uint256 currentIndex = nextLeafIndex;
        if (currentIndex >= (1 << TREE_DEPTH)) revert TreeFull();

        uint256 currentHash = leaf;
        for (uint256 i = 0; i < TREE_DEPTH; i++) {
            if (currentIndex % 2 == 0) {
                filledSubtrees[i] = currentHash;
                currentHash = hashLeftRight(currentHash, zeros[i]);
            } else {
                currentHash = hashLeftRight(filledSubtrees[i], currentHash);
            }
            currentIndex /= 2;
        }

        _addRoot(currentHash);
        index = nextLeafIndex;
        nextLeafIndex = nextLeafIndex + 1;
    }
}

