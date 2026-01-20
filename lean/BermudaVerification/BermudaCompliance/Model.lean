import BermudaVerification.BermudaCompliance.Spec
import BermudaVerification.Contracts.Model
import Mathlib.Data.Finset.Basic

namespace BermudaVerification
namespace Blockchain
namespace BermudaCompliance

abbrev Commitment := Nat
abbrev Root := Nat
abbrev Nullifier := Nat

/-- Off-chain compliance environment.

This models the *meaning* of on-chain Merkle roots:
- `validLicenses` corresponds to a license registry root.
- `kycLevels` corresponds to a KYC registry root.

The on-chain contract only sees roots; the ZK circuit witnesses the hidden
operator/sender and proves membership.
-/
structure Env where
  validLicenses : Finset Address
  kycLevels : Address → Option KYCLevel
  knownLicenseRoots : Finset Root
  knownKycRoots : Finset Root

/-- A minimal shielded pool state.

`notes` is a *spec-level* witness set of note commitments. On-chain, this is
represented by an incremental Merkle tree; withdrawals prove membership in a
known root.
-/
structure State where
  poolBalanceCents : Nat
  payouts : Address → Nat
  notes : Finset Commitment
  knownNoteRoots : Finset Root
  nullifiersUsed : Finset Nullifier

namespace State

def updatePayout (s : State) (recipient : Address) (f : Nat → Nat) : State :=
  { s with
    payouts := fun a =>
      if a = recipient then
        f (s.payouts a)
      else
        s.payouts a }

end State

/-- Deposit a note commitment into the pool.

`newRoot` is the post-state Merkle root (modeled abstractly). -/
structure DepositCall where
  note : Commitment
  amountCents : Nat
  newRoot : Root

/-- Withdraw from the pool.

The fields `operator` and `sender` are *private witnesses* from the ZK proof.
The on-chain contract only sees roots, recipient, amount, and nullifier.
-/
structure WithdrawCall where
  licenseRoot : Root
  kycRoot : Root
  noteRoot : Root
  nullifier : Nullifier
  recipient : Address
  amountCents : Nat
  note : Commitment
  operator : Address
  sender : Address

inductive Call where
  | deposit (d : DepositCall)
  | withdraw (w : WithdrawCall)

inductive Error where
  | unknownLicenseRoot
  | unknownKycRoot
  | unknownNoteRoot
  | nullifierAlreadyUsed
  | noteMissing
  | insufficientPoolBalance
  | noncompliant
  deriving DecidableEq, Repr

open BermudaVerification.Blockchain.Contracts.Model

def init : State :=
  { poolBalanceCents := 0
    payouts := fun _ => 0
    notes := ∅
    knownNoteRoots := ∅
    nullifiersUsed := ∅ }

def step (env : Env) (s : State) (c : Call) : Except Error State :=
  match c with
  | .deposit d =>
      .ok
        { s with
          poolBalanceCents := s.poolBalanceCents + d.amountCents
          notes := insert d.note s.notes
          knownNoteRoots := insert d.newRoot s.knownNoteRoots }
  | .withdraw w =>
      if w.licenseRoot ∈ env.knownLicenseRoots ∧
          w.kycRoot ∈ env.knownKycRoots ∧
          w.noteRoot ∈ s.knownNoteRoots then
        if w.nullifier ∉ s.nullifiersUsed then
          if w.note ∈ s.notes then
            if w.amountCents ≤ s.poolBalanceCents then
              if TransactionCompliant
                    w.operator
                    w.sender
                    w.amountCents
                    env.validLicenses
                    env.kycLevels then
                let s1 : State :=
                  { s with
                    poolBalanceCents := s.poolBalanceCents - w.amountCents
                    nullifiersUsed := insert w.nullifier s.nullifiersUsed }
                let s2 := s1.updatePayout w.recipient (fun x => x + w.amountCents)
                .ok s2
              else
                .error .noncompliant
            else
              .error .insufficientPoolBalance
          else
            .error .noteMissing
        else
          .error .nullifierAlreadyUsed
      else
        -- Preserve a stable error partition even though the on-chain contract
        -- would likely unify these checks.
        if w.licenseRoot ∈ env.knownLicenseRoots then
          if w.kycRoot ∈ env.knownKycRoots then
            .error .unknownNoteRoot
          else
            .error .unknownKycRoot
        else
          .error .unknownLicenseRoot

def model (env : Env) : ContractModel State Call Error :=
  { init := init
    step := step env }

end BermudaCompliance
end Blockchain
end BermudaVerification
