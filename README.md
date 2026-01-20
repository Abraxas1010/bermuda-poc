# Bermuda POC (Shielded Compliance Transfers)

This app is a **mostly-separate vertical slice** intended to be extracted from
HeytingLean later.

Goal: demonstrate **shielded accounting** (note commitments + nullifiers) while
enforcing a minimal Bermuda-style compliance rule:

- A licensed operator processes the transfer.
- The sender has a KYC level whose per-tx limit covers the amount.

Privacy target (Option B): on-chain reveals **recipient + amount + nullifier**,
but hides **sender identity, operator identity, and KYC level**.

## Directory layout

- `contracts/`: Solidity contracts (registries + shielded pool + verifier shim)
- `circuits/`: Circom circuits (membership + compliance + nullifier)
- `docs/`: design notes and implementation checklist

## Relationship to Lean

The formal spec/model/proofs live in:

- `lean/HeytingLean/Blockchain/BermudaCompliance/`

Those modules are written to be easy to extract into a standalone Lean project.

## Build (local)

```bash
cd apps/bermuda-poc

# Compile Solidity
npm run compile

# Compile circuits (requires `circom`)
npm run compile:circuits

# Generate Groth16 verifiers (slow the first time; fast incremental afterwards)
npm run build:verifiers

# Run local E2E tests (generates proofs at runtime)
npx hardhat test
```
