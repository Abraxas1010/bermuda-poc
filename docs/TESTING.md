# Testing

This app’s tests are meant to be “end-to-end local”:

- deploy contracts to the Hardhat in-memory chain
- generate Groth16 proofs from the compiled circuit WASM + zkey
- submit proofs on-chain and assert expected success/failure

Run:

```bash
cd apps/bermuda-poc
npx hardhat test
```

## Merkle paths (important detail)

The withdrawal circuit verifies **Merkle membership** for:

- operator license leaf ∈ `licenseRoot`
- sender KYC leaf ∈ `kycRoot`
- note commitment leaf ∈ `noteRoot`

To avoid “accidentally passing” with trivial paths, the withdraw test does
**not** use `leafIndex = 0`.

Instead, `apps/bermuda-poc/test/withdrawProof.test.js` inserts multiple leaves
and proves membership of `leafIndex = 3` (the 4th leaf), which forces a more
realistic mix of `pathIndices` bits.

### How the path is computed

The test computes `(pathElements, pathIndices)` from the full set of inserted
leaves using the registry’s *exact* on-chain hash:

- hash function: `BermudaMerkleRegistry.hashLeftRight(left, right)`
- zero values: `BermudaMerkleRegistry.zeros(level)`

This is deliberate: it ensures the test’s off-chain Merkle computation matches
the registry’s Poseidon(2) hashing and its zero padding strategy.

## Deposit binding

Deposits are protected by a ZK proof that the public `(amount, commitment)` pair
is well-formed.

- Circuit: `circuits/bermudaNoteDeposit.circom`
- Contract: `BermudaCompliantShieldedPool.deposit(Groth16Proof, BermudaDepositInputs)`

The deposit test checks both:

- a valid commitment is accepted
- a malformed commitment (changing the public `commitment` while reusing the proof)
  is rejected

