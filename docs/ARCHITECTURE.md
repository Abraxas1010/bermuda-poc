# Architecture (draft)

This folder will track the concrete on-chain + ZK design.

Lean reference model: `lean/HeytingLean/Blockchain/BermudaCompliance/Model.lean`.

## Target system (Option B)

### On-chain

- **License registry** (Merkle root history)
  - Holds a Merkle tree of “valid operator license” credential leaves.
  - Exposes `isKnownRoot(root)`.

- **KYC registry** (Merkle root history)
  - Holds a Merkle tree of “(address, kyc level)” credential leaves.
  - Exposes `isKnownRoot(root)`.

- **Shielded pool**
  - Holds the ERC20 funds (e.g. USDC).
  - Holds a Merkle root history of **note commitments**.
  - Tracks spent **nullifiers** (`nullifierUsed[nullifier] = true`) to prevent double spends.
  - Withdrawal verifies a ZK proof and transfers to `recipient`.

### ZK statement (high level)

Public inputs:
- `licenseRoot`, `kycRoot`, `noteRoot`
- `nullifier`
- `recipient`
- `amount`

Private witnesses:
- `operator` (licensed)
- `sender` (has KYC)
- KYC level (or encoding thereof)
- note secret / note commitment membership proof

Constraints:
- `operator` is a member of `licenseRoot`.
- `sender` is a member of `kycRoot` with some `kycLevel`.
- `amount ≤ limit(kycLevel)`.
- note commitment is a member of `noteRoot`.
- `nullifier` is correctly derived from the note secret (and optionally binds `operator` and `amount`).

## Standard leaf/commitment formats (v0)

To prevent drift between contracts/circuit/scripts, we standardize on Poseidon(2)
composition patterns implemented in the registries:

- License leaf: `BermudaLicenseRegistry.computeLicenseLeaf(...)`
- KYC leaf: `BermudaKYCRegistry.computeKycLeaf(...)`
- Note commitment: `BermudaNoteRegistry.computeNoteCommitment(...)`

## Deposit binding (Option A)

Deposits are verified with a ZK proof that the public `(amount, commitment)`
pair is well-formed:

- Circuit: `apps/bermuda-poc/circuits/bermudaNoteDeposit.circom`
- On-chain: `BermudaCompliantShieldedPool.deposit(Groth16Proof, BermudaDepositInputs)`
- Verifier build: `cd apps/bermuda-poc && npm run build:verifiers`

## Lean ↔ Solidity mapping

The Lean model is intentionally a spec-level model of the verifier:

- `State.notes : Finset Commitment` is a *witness set* of commitments (on-chain these live in a Merkle tree).
- `State.knownNoteRoots : Finset Root` corresponds to the on-chain note root history.
- `State.nullifiersUsed : Finset Nullifier` corresponds to `nullifierUsed[.]`.
- `Env.validLicenses` / `Env.kycLevels` model the *meaning* of the license/KYC roots.

Immediate next step: implement Solidity so the contract state + guards mirror
the Lean `step` function.
