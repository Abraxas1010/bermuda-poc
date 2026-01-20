import BermudaVerification.BermudaCompliance.Model
import Mathlib.Tactic

namespace BermudaVerification
namespace Blockchain
namespace BermudaCompliance

theorem withdraw_ok_preconditions
    (env : Env) (s s' : State) (w : WithdrawCall)
    (h : step env s (.withdraw w) = .ok s') :
    w.licenseRoot ∈ env.knownLicenseRoots ∧
      w.kycRoot ∈ env.knownKycRoots ∧
      w.noteRoot ∈ s.knownNoteRoots ∧
      w.nullifier ∉ s.nullifiersUsed ∧
      w.note ∈ s.notes ∧
      w.amountCents ≤ s.poolBalanceCents ∧
      TransactionCompliant w.operator w.sender w.amountCents env.validLicenses env.kycLevels := by
  classical
  by_cases hLic : w.licenseRoot ∈ env.knownLicenseRoots
  · by_cases hKyc : w.kycRoot ∈ env.knownKycRoots
    · by_cases hNoteRoot : w.noteRoot ∈ s.knownNoteRoots
      · by_cases hNull : w.nullifier ∉ s.nullifiersUsed
        · by_cases hNote : w.note ∈ s.notes
          · by_cases hBal : w.amountCents ≤ s.poolBalanceCents
            · by_cases hComp :
                TransactionCompliant
                  w.operator w.sender w.amountCents env.validLicenses env.kycLevels
              · exact ⟨hLic, hKyc, hNoteRoot, hNull, hNote, hBal, hComp⟩
              · -- noncompliant branch cannot return `.ok`
                have : step env s (.withdraw w) = .error .noncompliant := by
                  simp [step, hLic, hKyc, hNoteRoot, hNull, hNote, hBal, hComp]
                cases (Eq.trans (Eq.symm this) h)
            · have : step env s (.withdraw w) = .error .insufficientPoolBalance := by
                simp [step, hLic, hKyc, hNoteRoot, hNull, hNote, hBal]
              cases (Eq.trans (Eq.symm this) h)
          · have : step env s (.withdraw w) = .error .noteMissing := by
              simp [step, hLic, hKyc, hNoteRoot, hNull, hNote]
            cases (Eq.trans (Eq.symm this) h)
        · have : step env s (.withdraw w) = .error .nullifierAlreadyUsed := by
            simp [step, hLic, hKyc, hNoteRoot, hNull]
          cases (Eq.trans (Eq.symm this) h)
      · have : step env s (.withdraw w) = .error .unknownNoteRoot := by
          simp [step, hLic, hKyc, hNoteRoot]
        cases (Eq.trans (Eq.symm this) h)
    · have : step env s (.withdraw w) = .error .unknownKycRoot := by
        simp [step, hLic, hKyc]
      cases (Eq.trans (Eq.symm this) h)
  · have : step env s (.withdraw w) = .error .unknownLicenseRoot := by
      simp [step, hLic]
    cases (Eq.trans (Eq.symm this) h)

theorem withdraw_ok_implies_compliant
    (env : Env) (s s' : State) (w : WithdrawCall)
    (h : step env s (.withdraw w) = .ok s') :
    TransactionCompliant w.operator w.sender w.amountCents env.validLicenses env.kycLevels := by
  exact (withdraw_ok_preconditions env s s' w h).2.2.2.2.2.2

theorem withdraw_ok_state_eq
    (env : Env) (s s' : State) (w : WithdrawCall)
    (h : step env s (.withdraw w) = .ok s') :
    ∃ s1 s2,
      s1 =
          { s with
            poolBalanceCents := s.poolBalanceCents - w.amountCents
            nullifiersUsed := insert w.nullifier s.nullifiersUsed } ∧
        s2 = s1.updatePayout w.recipient (fun x => x + w.amountCents) ∧
        s' = s2 := by
  classical
  obtain ⟨hLic, hKyc, hNoteRoot, hNull, hNote, hBal, hComp⟩ :=
    withdraw_ok_preconditions env s s' w h
  let s1 : State :=
    { s with
      poolBalanceCents := s.poolBalanceCents - w.amountCents
      nullifiersUsed := insert w.nullifier s.nullifiersUsed }
  let s2 : State := s1.updatePayout w.recipient (fun x => x + w.amountCents)
  have hs2 : step env s (.withdraw w) = .ok s2 := by
    simp [step, hLic, hKyc, hNoteRoot, hNull, hNote, hBal, hComp, s1, s2]
  have : s' = s2 := by
    -- compare the two successful evaluations
    have hOk : (.ok s' : Except Error State) = .ok s2 := by
      exact Eq.trans (Eq.symm h) hs2
    let unwrap : Except Error State → State
      | .ok v => v
      | .error _ => s'
    have : unwrap (.ok s') = unwrap (.ok s2) := congrArg unwrap hOk
    simpa [unwrap] using this
  refine ⟨s1, s2, rfl, rfl, this⟩

theorem withdraw_ok_marks_nullifier
    (env : Env) (s s' : State) (w : WithdrawCall)
    (h : step env s (.withdraw w) = .ok s') :
    w.nullifier ∈ s'.nullifiersUsed := by
  classical
  obtain ⟨s1, s2, hs1, hs2, hs'⟩ := withdraw_ok_state_eq env s s' w h
  subst hs'
  subst hs2
  subst hs1
  simp [State.updatePayout]

theorem withdraw_ok_increases_recipient_payout
    (env : Env) (s s' : State) (w : WithdrawCall)
    (h : step env s (.withdraw w) = .ok s') :
    s'.payouts w.recipient = s.payouts w.recipient + w.amountCents := by
  classical
  obtain ⟨s1, s2, hs1, hs2, hs'⟩ := withdraw_ok_state_eq env s s' w h
  subst hs'
  subst hs2
  subst hs1
  simp [State.updatePayout]

end BermudaCompliance
end Blockchain
end BermudaVerification
