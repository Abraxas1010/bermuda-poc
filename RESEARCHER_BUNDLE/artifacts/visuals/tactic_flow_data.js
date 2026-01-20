const tacticFlowData = {
  theorems: [
    {
      name: "withdraw_ok_preconditions",
      file: "BermudaCompliance/Proofs.lean",
      description: "All preconditions must hold for successful withdrawal",
      statement: "step env s (.withdraw w) = .ok s' → (7 conjuncts)",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ preconditions hold", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "classical", depth: 1 },
        { id: "by_cases_2", type: "tactic", label: "by_cases hLic : w.licenseRoot ∈ env.knownLicenseRoots", depth: 1 },
        { id: "by_cases_3", type: "tactic", label: "by_cases hKyc : w.kycRoot ∈ env.knownKycRoots", depth: 2 },
        { id: "by_cases_4", type: "tactic", label: "by_cases hNoteRoot", depth: 3 },
        { id: "by_cases_5", type: "tactic", label: "by_cases hNull", depth: 4 },
        { id: "by_cases_6", type: "tactic", label: "by_cases hNote", depth: 5 },
        { id: "by_cases_7", type: "tactic", label: "by_cases hBal", depth: 6 },
        { id: "by_cases_8", type: "tactic", label: "by_cases hComp : TransactionCompliant", depth: 7 },
        { id: "exact_9", type: "tactic", label: "exact ⟨hLic, hKyc, ..., hComp⟩", depth: 8 },
        { id: "qed_10", type: "qed", label: "QED", depth: 9 },
        { id: "simp_11", type: "simp_trace", label: "simp [step, ...] (contradiction)", depth: 8 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "by_cases_2" },
        { from: "by_cases_2", to: "by_cases_3" },
        { from: "by_cases_3", to: "by_cases_4" },
        { from: "by_cases_4", to: "by_cases_5" },
        { from: "by_cases_5", to: "by_cases_6" },
        { from: "by_cases_6", to: "by_cases_7" },
        { from: "by_cases_7", to: "by_cases_8" },
        { from: "by_cases_8", to: "exact_9" },
        { from: "exact_9", to: "qed_10" },
        { from: "by_cases_8", to: "simp_11" }
      ]
    },
    {
      name: "withdraw_ok_implies_compliant",
      file: "BermudaCompliance/Proofs.lean",
      description: "Successful withdrawal implies compliance",
      statement: "step env s (.withdraw w) = .ok s' → TransactionCompliant w",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ TransactionCompliant w.operator w.sender w.amount", depth: 0 },
        { id: "exact_1", type: "tactic", label: "exact (withdraw_ok_preconditions ...).2.2.2.2.2.2", depth: 1 },
        { id: "hyp_2", type: "hypothesis", label: "uses: withdraw_ok_preconditions", depth: 1 },
        { id: "qed_3", type: "qed", label: "QED", depth: 2 }
      ],
      edges: [
        { from: "goal_0", to: "exact_1" },
        { from: "exact_1", to: "hyp_2" },
        { from: "exact_1", to: "qed_3" }
      ]
    },
    {
      name: "withdraw_ok_state_eq",
      file: "BermudaCompliance/Proofs.lean",
      description: "Exact state after successful withdrawal",
      statement: "∃ s1 s2, s1 = {state with updates} ∧ s2 = s1.updatePayout ∧ s' = s2",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ ∃ s1 s2, state equality", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "classical", depth: 1 },
        { id: "obtain_2", type: "tactic", label: "obtain ⟨hLic, ...⟩ := withdraw_ok_preconditions", depth: 1 },
        { id: "let_3", type: "tactic", label: "let s1 := {state updates}", depth: 2 },
        { id: "let_4", type: "tactic", label: "let s2 := s1.updatePayout", depth: 2 },
        { id: "have_5", type: "tactic", label: "have hs2 : step env s (.withdraw w) = .ok s2", depth: 2 },
        { id: "simp_6", type: "simp_trace", label: "simp [step, preconditions, s1, s2]", depth: 3 },
        { id: "have_7", type: "tactic", label: "have : s' = s2", depth: 2 },
        { id: "refine_8", type: "tactic", label: "refine ⟨s1, s2, rfl, rfl, this⟩", depth: 2 },
        { id: "qed_9", type: "qed", label: "QED", depth: 3 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "obtain_2" },
        { from: "obtain_2", to: "let_3" },
        { from: "let_3", to: "let_4" },
        { from: "let_4", to: "have_5" },
        { from: "have_5", to: "simp_6" },
        { from: "let_4", to: "have_7" },
        { from: "have_7", to: "refine_8" },
        { from: "refine_8", to: "qed_9" }
      ]
    },
    {
      name: "withdraw_ok_marks_nullifier",
      file: "BermudaCompliance/Proofs.lean",
      description: "Nullifier is marked after withdrawal",
      statement: "w.nullifier ∈ s'.nullifiersUsed",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ w.nullifier ∈ s'.nullifiersUsed", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "classical", depth: 1 },
        { id: "obtain_2", type: "tactic", label: "obtain ⟨s1, s2, hs1, hs2, hs'⟩ := withdraw_ok_state_eq", depth: 1 },
        { id: "subst_3", type: "tactic", label: "subst hs' hs2 hs1", depth: 2 },
        { id: "simp_4", type: "simp_trace", label: "simp [State.updatePayout]", depth: 2 },
        { id: "qed_5", type: "qed", label: "QED", depth: 3 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "obtain_2" },
        { from: "obtain_2", to: "subst_3" },
        { from: "subst_3", to: "simp_4" },
        { from: "simp_4", to: "qed_5" }
      ]
    },
    {
      name: "withdraw_ok_increases_recipient_payout",
      file: "BermudaCompliance/Proofs.lean",
      description: "Recipient receives exact amount",
      statement: "s'.payouts w.recipient = s.payouts w.recipient + w.amountCents",
      nodes: [
        { id: "goal_0", type: "goal", label: "⊢ s'.payouts recipient = s.payouts recipient + amount", depth: 0 },
        { id: "tactic_1", type: "tactic", label: "classical", depth: 1 },
        { id: "obtain_2", type: "tactic", label: "obtain ⟨s1, s2, hs1, hs2, hs'⟩ := withdraw_ok_state_eq", depth: 1 },
        { id: "subst_3", type: "tactic", label: "subst hs' hs2 hs1", depth: 2 },
        { id: "simp_4", type: "simp_trace", label: "simp [State.updatePayout]", depth: 2 },
        { id: "qed_5", type: "qed", label: "QED", depth: 3 }
      ],
      edges: [
        { from: "goal_0", to: "tactic_1" },
        { from: "tactic_1", to: "obtain_2" },
        { from: "obtain_2", to: "subst_3" },
        { from: "subst_3", to: "simp_4" },
        { from: "simp_4", to: "qed_5" }
      ]
    }
  ]
};
