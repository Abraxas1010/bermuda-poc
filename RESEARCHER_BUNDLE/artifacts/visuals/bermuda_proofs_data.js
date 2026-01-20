const bermudaProofsData = {
  items: [
    // CCI/Core Module
    { name: "Address", kind: "abbrev", family: "CCI/Core", pos: { x: 0.15, y: 0.2, z: 0.1 } },

    // Contracts/Spec Module
    { name: "Contract.Spec", kind: "structure", family: "Contracts/Spec", pos: { x: 0.3, y: 0.15, z: 0.2 } },

    // Contracts/Model Module
    { name: "Contract.Model", kind: "structure", family: "Contracts/Model", pos: { x: 0.35, y: 0.25, z: 0.25 } },

    // BermudaCompliance/Spec Module
    { name: "KYCLevel", kind: "inductive", family: "BermudaCompliance/Spec", pos: { x: 0.5, y: 0.3, z: 0.3 } },
    { name: "txLimitCents", kind: "def", family: "BermudaCompliance/Spec", pos: { x: 0.55, y: 0.35, z: 0.35 } },
    { name: "TransactionCompliant", kind: "def", family: "BermudaCompliance/Spec", pos: { x: 0.6, y: 0.4, z: 0.4 } },

    // BermudaCompliance/Model Module
    { name: "Env", kind: "structure", family: "BermudaCompliance/Model", pos: { x: 0.4, y: 0.55, z: 0.45 } },
    { name: "State", kind: "structure", family: "BermudaCompliance/Model", pos: { x: 0.45, y: 0.6, z: 0.5 } },
    { name: "WithdrawCall", kind: "structure", family: "BermudaCompliance/Model", pos: { x: 0.5, y: 0.65, z: 0.55 } },
    { name: "Error", kind: "inductive", family: "BermudaCompliance/Model", pos: { x: 0.55, y: 0.7, z: 0.6 } },
    { name: "Action", kind: "inductive", family: "BermudaCompliance/Model", pos: { x: 0.6, y: 0.75, z: 0.65 } },
    { name: "step", kind: "def", family: "BermudaCompliance/Model", pos: { x: 0.65, y: 0.8, z: 0.7 } },
    { name: "State.updatePayout", kind: "def", family: "BermudaCompliance/Model", pos: { x: 0.5, y: 0.85, z: 0.75 } },

    // BermudaCompliance/Proofs Module
    { name: "withdraw_ok_preconditions", kind: "theorem", family: "BermudaCompliance/Proofs", pos: { x: 0.75, y: 0.5, z: 0.35 } },
    { name: "withdraw_ok_implies_compliant", kind: "theorem", family: "BermudaCompliance/Proofs", pos: { x: 0.8, y: 0.55, z: 0.4 } },
    { name: "withdraw_ok_state_eq", kind: "theorem", family: "BermudaCompliance/Proofs", pos: { x: 0.78, y: 0.65, z: 0.5 } },
    { name: "withdraw_ok_marks_nullifier", kind: "theorem", family: "BermudaCompliance/Proofs", pos: { x: 0.82, y: 0.7, z: 0.55 } },
    { name: "withdraw_ok_increases_recipient_payout", kind: "theorem", family: "BermudaCompliance/Proofs", pos: { x: 0.85, y: 0.75, z: 0.6 } }
  ],
  edges: [
    [0, 2],  // Address -> Contract.Model
    [1, 2],  // Contract.Spec -> Contract.Model
    [2, 6],  // Contract.Model -> Env
    [3, 4],  // KYCLevel -> txLimitCents
    [4, 5],  // txLimitCents -> TransactionCompliant
    [5, 11], // TransactionCompliant -> step
    [6, 11], // Env -> step
    [7, 11], // State -> step
    [8, 11], // WithdrawCall -> step
    [9, 11], // Error -> step
    [10, 11], // Action -> step
    [7, 12], // State -> updatePayout
    [11, 13], // step -> withdraw_ok_preconditions
    [13, 14], // withdraw_ok_preconditions -> withdraw_ok_implies_compliant
    [13, 15], // withdraw_ok_preconditions -> withdraw_ok_state_eq
    [15, 16], // withdraw_ok_state_eq -> withdraw_ok_marks_nullifier
    [15, 17], // withdraw_ok_state_eq -> withdraw_ok_increases_recipient_payout
    [12, 16], // updatePayout -> withdraw_ok_marks_nullifier
    [12, 17]  // updatePayout -> withdraw_ok_increases_recipient_payout
  ]
};

const colors = {
  'CCI/Core': '#a3a3a3',
  'Contracts/Spec': '#5e9cff',
  'Contracts/Model': '#5e9cff',
  'BermudaCompliance/Spec': '#c77dff',
  'BermudaCompliance/Model': '#4ade80',
  'BermudaCompliance/Proofs': '#f472b6'
};
