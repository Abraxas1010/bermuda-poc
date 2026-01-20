# Circuits

This folder contains Circom circuits for the Bermuda shielded compliance POC.

## Entry points

- `bermudaWithdrawCompliance.circom`
  - Proves: license membership + KYC membership + amount≤limit + note membership + nullifier derivation.
  - Public inputs match the Solidity pool’s `withdraw` ABI.

- `bermudaNoteDeposit.circom`
  - Optional (future wiring): proves a note commitment binds `(noteSecret, noteSalt, amount)`.
  - Intended to prevent “deposit amount / commitment mismatch” attacks.

## Includes

We vendor small wrappers in `circuits/lib/` and rely on `circomlib` for Poseidon
and comparators.

