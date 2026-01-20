const proofTermData = {
  theorems: [
    {
      name: "withdraw_ok_preconditions",
      file: "BermudaCompliance/Proofs.lean",
      description: "All preconditions must hold for successful withdrawal",
      statement: "7 conjuncts: license, kyc, noteRoot, nullifier, note, balance, compliant",
      nodes: [
        { id: "root", type: "lam", label: "fun env s s' w h =>", depth: 0 },
        { id: "by_cases", type: "app", label: "Classical.byCases (nested)", depth: 1 },
        { id: "branch1", type: "lam", label: "hLic =>", depth: 2 },
        { id: "branch2", type: "lam", label: "hKyc =>", depth: 3 },
        { id: "branch3", type: "lam", label: "hNoteRoot =>", depth: 4 },
        { id: "branch4", type: "lam", label: "hNull =>", depth: 5 },
        { id: "branch5", type: "lam", label: "hNote =>", depth: 6 },
        { id: "branch6", type: "lam", label: "hBal =>", depth: 7 },
        { id: "branch7", type: "lam", label: "hComp =>", depth: 8 },
        { id: "and_intro", type: "app", label: "And.intro (nested)", depth: 9 },
        { id: "contra", type: "app", label: "absurd (contradiction)", depth: 9 }
      ],
      edges: [
        { from: "root", to: "by_cases" },
        { from: "by_cases", to: "branch1" },
        { from: "branch1", to: "branch2" },
        { from: "branch2", to: "branch3" },
        { from: "branch3", to: "branch4" },
        { from: "branch4", to: "branch5" },
        { from: "branch5", to: "branch6" },
        { from: "branch6", to: "branch7" },
        { from: "branch7", to: "and_intro" },
        { from: "branch7", to: "contra" }
      ]
    },
    {
      name: "withdraw_ok_implies_compliant",
      file: "BermudaCompliance/Proofs.lean",
      description: "Successful withdrawal implies compliance",
      statement: "TransactionCompliant w.operator w.sender w.amountCents",
      nodes: [
        { id: "root", type: "app", label: "And.right (projected)", depth: 0 },
        { id: "preconds", type: "app", label: "withdraw_ok_preconditions", depth: 1 },
        { id: "env", type: "var", label: "env", depth: 2 },
        { id: "s", type: "var", label: "s", depth: 2 },
        { id: "s'", type: "var", label: "s'", depth: 2 },
        { id: "w", type: "var", label: "w", depth: 2 },
        { id: "h", type: "var", label: "h", depth: 2 }
      ],
      edges: [
        { from: "root", to: "preconds" },
        { from: "preconds", to: "env" },
        { from: "preconds", to: "s" },
        { from: "preconds", to: "s'" },
        { from: "preconds", to: "w" },
        { from: "preconds", to: "h" }
      ]
    },
    {
      name: "withdraw_ok_state_eq",
      file: "BermudaCompliance/Proofs.lean",
      description: "Exact state after successful withdrawal",
      statement: "∃ s1 s2, s1 = {...} ∧ s2 = s1.updatePayout ∧ s' = s2",
      nodes: [
        { id: "root", type: "app", label: "Exists.intro", depth: 0 },
        { id: "s1_def", type: "app", label: "s1 := {state updates}", depth: 1 },
        { id: "inner", type: "app", label: "Exists.intro", depth: 1 },
        { id: "s2_def", type: "app", label: "s2 := s1.updatePayout", depth: 2 },
        { id: "and_triple", type: "app", label: "And.intro", depth: 2 },
        { id: "rfl1", type: "const", label: "rfl", depth: 3 },
        { id: "and_inner", type: "app", label: "And.intro", depth: 3 },
        { id: "rfl2", type: "const", label: "rfl", depth: 4 },
        { id: "eq_proof", type: "app", label: "Eq.trans h hs2", depth: 4 }
      ],
      edges: [
        { from: "root", to: "s1_def" },
        { from: "root", to: "inner" },
        { from: "inner", to: "s2_def" },
        { from: "inner", to: "and_triple" },
        { from: "and_triple", to: "rfl1" },
        { from: "and_triple", to: "and_inner" },
        { from: "and_inner", to: "rfl2" },
        { from: "and_inner", to: "eq_proof" }
      ]
    },
    {
      name: "withdraw_ok_marks_nullifier",
      file: "BermudaCompliance/Proofs.lean",
      description: "Nullifier is marked after withdrawal",
      statement: "w.nullifier ∈ s'.nullifiersUsed",
      nodes: [
        { id: "root", type: "app", label: "proof term", depth: 0 },
        { id: "obtain", type: "app", label: "withdraw_ok_state_eq.elim", depth: 1 },
        { id: "lam1", type: "lam", label: "fun s1 => ...", depth: 2 },
        { id: "elim2", type: "app", label: "Exists.elim", depth: 3 },
        { id: "lam2", type: "lam", label: "fun s2 => ...", depth: 4 },
        { id: "subst_chain", type: "app", label: "Eq.subst (chain)", depth: 5 },
        { id: "simp_result", type: "app", label: "Finset.mem_insert_self", depth: 6 }
      ],
      edges: [
        { from: "root", to: "obtain" },
        { from: "obtain", to: "lam1" },
        { from: "lam1", to: "elim2" },
        { from: "elim2", to: "lam2" },
        { from: "lam2", to: "subst_chain" },
        { from: "subst_chain", to: "simp_result" }
      ]
    },
    {
      name: "withdraw_ok_increases_recipient_payout",
      file: "BermudaCompliance/Proofs.lean",
      description: "Recipient receives exact amount",
      statement: "s'.payouts w.recipient = s.payouts w.recipient + w.amountCents",
      nodes: [
        { id: "root", type: "app", label: "proof term", depth: 0 },
        { id: "obtain", type: "app", label: "withdraw_ok_state_eq.elim", depth: 1 },
        { id: "subst", type: "app", label: "subst hs' hs2 hs1", depth: 2 },
        { id: "simp", type: "app", label: "simp [State.updatePayout]", depth: 3 },
        { id: "result", type: "const", label: "rfl", depth: 4 }
      ],
      edges: [
        { from: "root", to: "obtain" },
        { from: "obtain", to: "subst" },
        { from: "subst", to: "simp" },
        { from: "simp", to: "result" }
      ]
    }
  ]
};
