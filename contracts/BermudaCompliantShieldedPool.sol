// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./interfaces/IERC20Minimal.sol";
import "./interfaces/ICredentialRootRegistry.sol";
import "./interfaces/INoteRegistry.sol";
import "./zk/BermudaZKTypes.sol";

/// @title BermudaCompliantShieldedPool
/// @notice Shielded note pool with a ZK compliance gate.
/// @dev This is a scaffold: the Merkle tree and concrete proof format are wired
///      up in subsequent steps. For now, it captures the contract *shape* and
///      the on-chain checks corresponding to the Lean model.
contract BermudaCompliantShieldedPool {
    IERC20Minimal public immutable token;
    ICredentialRootRegistry public immutable licenseRegistry;
    ICredentialRootRegistry public immutable kycRegistry;
    INoteRegistry public immutable noteRegistry;
    IBermudaWithdrawVerifier public immutable withdrawVerifier;
    IBermudaDepositVerifier public immutable depositVerifier;

    mapping(uint256 => bool) public nullifierUsed;

    event Deposit(uint256 indexed commitment, uint256 amount, uint256 noteRoot);
    event Withdraw(uint256 indexed nullifier, address indexed recipient, uint256 amount);

    error InvalidLicenseRoot();
    error InvalidKycRoot();
    error InvalidNoteRoot();
    error NullifierAlreadyUsed();
    error InvalidProof();
    error TransferFailed();

    constructor(
        address token_,
        address licenseRegistry_,
        address kycRegistry_,
        address noteRegistry_,
        address withdrawVerifier_,
        address depositVerifier_
    ) {
        token = IERC20Minimal(token_);
        licenseRegistry = ICredentialRootRegistry(licenseRegistry_);
        kycRegistry = ICredentialRootRegistry(kycRegistry_);
        noteRegistry = INoteRegistry(noteRegistry_);
        withdrawVerifier = IBermudaWithdrawVerifier(withdrawVerifier_);
        depositVerifier = IBermudaDepositVerifier(depositVerifier_);
    }

    /// @notice Deposit tokens and insert a note commitment into the note registry.
    function deposit(Groth16Proof calldata proof, BermudaDepositInputs calldata inputs) external {
        if (!depositVerifier.verifyDeposit(proof, inputs)) revert InvalidProof();
        if (!token.transferFrom(msg.sender, address(this), inputs.amount)) revert TransferFailed();

        noteRegistry.addLeaf(inputs.commitment);
        emit Deposit(inputs.commitment, inputs.amount, noteRegistry.getMerkleRoot());
    }

    /// @notice Withdraw to a public recipient, gated by a ZK compliance proof.
    function withdraw(Groth16Proof calldata proof, BermudaWithdrawInputs calldata inputs) external {
        if (!licenseRegistry.isKnownRoot(inputs.licenseRoot)) revert InvalidLicenseRoot();
        if (!kycRegistry.isKnownRoot(inputs.kycRoot)) revert InvalidKycRoot();
        if (!noteRegistry.isKnownRoot(inputs.noteRoot)) revert InvalidNoteRoot();

        if (nullifierUsed[inputs.nullifier]) revert NullifierAlreadyUsed();

        if (!withdrawVerifier.verifyWithdraw(proof, inputs)) revert InvalidProof();

        nullifierUsed[inputs.nullifier] = true;

        address recipient = address(uint160(inputs.recipient));
        if (!token.transfer(recipient, inputs.amount)) revert TransferFailed();
        emit Withdraw(inputs.nullifier, recipient, inputs.amount);
    }
}
