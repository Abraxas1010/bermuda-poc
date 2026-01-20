<img src="assets/Apoth3osis.webp" alt="Apoth3osis Logo" width="140"/>

<sub><strong>Our tech stack is ontological:</strong><br>
<strong>Hardware — Physics</strong><br>
<strong>Software — Mathematics</strong><br><br>
<strong>Our engineering workflow is simple:</strong> discover, build, grow, learn & teach</sub>

---

<sub>
<strong>Notice of Proprietary Information</strong><br>
This document outlines foundational concepts and methodologies developed during internal research and development at Apoth3osis. To protect our intellectual property and adhere to client confidentiality agreements, the code, architectural details, and performance metrics presented herein may be simplified, redacted, or presented for illustrative purposes only. This paper is intended to share our conceptual approach and does not represent the full complexity, scope, or performance of our production-level systems. The complete implementation and its derivatives remain proprietary.
</sub>

---

# Bermuda POC (Shielded Compliance Transfers)

[![Lean 4](https://img.shields.io/badge/Lean-4.17.0-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAzMiAzMiI+PHBhdGggZmlsbD0iI2ZmZiIgZD0iTTE2IDJMMiAxNmwxNCAxNCAxNC0xNHoiLz48L3N2Zz4=)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.24.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apoth3osis%20Stack%20v1-orange)](LICENSE.md)
[![Sorry Count](https://img.shields.io/badge/sorry-0-brightgreen)]()

## Credo

> *"Privacy is not secrecy. A private matter is something one doesn't want the whole world to know, but a secret matter is something one doesn't want anybody to know. Privacy is the power to selectively reveal oneself to the world."*
> — **Eric Hughes**, *A Cypherpunk's Manifesto*

In regulated finance, privacy and compliance are often seen as opposing forces. Bermuda demonstrates they can coexist: users maintain privacy over sensitive data (identity, operator, KYC level) while the system mathematically guarantees regulatory compliance. This is not security through obscurity—it's cryptographic certainty backed by formal proofs.

### Acknowledgment

We humbly thank the collective intelligence of humanity for providing the technology and culture we cherish. We do our best to properly reference the authors of the works utilized herein, though we may occasionally fall short. Our formalization acts as a reciprocal validation—confirming the structural integrity of their original insights while securing the foundation upon which we build. In truth, all creative work is derivative; we stand on the shoulders of those who came before, and our contributions are simply the next link in an unbroken chain of human ingenuity.

---

**Machine-checked formalization of shielded compliance transfers with ZK proofs for privacy-preserving KYC verification.**

<table>
<tr>
<td align="center" width="50%">
<strong>2D Proof Map</strong><br/>
<em>Click to explore: pan, zoom, search declarations</em><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/bermuda_2d.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/bermuda_2d_preview.svg" alt="UMAP 2D preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/bermuda_2d.html">▶ Open Interactive 2D Map</a>
</td>
<td align="center" width="50%">
<strong>3D Proof Map</strong><br/>
<em>Click to explore: rotate, zoom, click nodes</em><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/bermuda_3d.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/bermuda_3d_preview.svg" alt="UMAP 3D preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/bermuda_3d.html">▶ Open Interactive 3D Map</a>
</td>
</tr>
<tr>
<td align="center" width="50%">
<strong>Tactic Flow Graph</strong><br/>
<em>Proof tactics and goal transformations</em><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/tactic_flow.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/tactic_flow_preview.svg" alt="Tactic Flow preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/tactic_flow.html">▶ Open Interactive Tactic Flow</a>
</td>
<td align="center" width="50%">
<strong>Proof Term DAG</strong><br/>
<em>Abstract syntax tree of proof terms</em><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/proof_term_dag.html">
  <img src="RESEARCHER_BUNDLE/artifacts/visuals/proof_term_dag_preview.svg" alt="Proof Term DAG preview" width="100%"/>
</a><br/>
<a href="https://abraxas1010.github.io/bermuda-poc/RESEARCHER_BUNDLE/artifacts/visuals/proof_term_dag.html">▶ Open Interactive Proof DAG</a>
</td>
</tr>
</table>

---

## Overview

This repository provides:

1. **Solidity Contracts** — Shielded pool, operator registry, KYC registry, verifier contracts
2. **Circom Circuits** — ZK proofs for membership, compliance, and nullifier management
3. **Lean 4 Verification** — Machine-checked proofs of compliance and state transition correctness

## Key Results

| Theorem | Description | Significance |
|---------|-------------|--------------|
| `withdraw_ok_preconditions` | All preconditions must hold for successful withdrawal | Complete characterization of valid withdrawals |
| `withdraw_ok_implies_compliant` | Successful withdrawal implies compliance | Core compliance guarantee |
| `withdraw_ok_marks_nullifier` | Nullifier is marked after withdrawal | Prevents double-spending |
| `withdraw_ok_increases_recipient_payout` | Recipient receives exact amount | Balance correctness |

---

## What the Proofs Guarantee

### For Regulators and Compliance Officers

| Property | What It Means | Why It Matters |
|----------|---------------|----------------|
| **Compliance Guarantee** | Every withdrawal satisfies KYC/AML requirements | Mathematical certainty of regulatory compliance |
| **Licensed Operators** | Only authorized operators can process transfers | Regulatory oversight maintained |
| **KYC Limits** | Transaction amounts respect KYC tier limits | Automatic enforcement of regulations |
| **No Double-Spend** | Nullifiers prevent replay attacks | Each note can only be withdrawn once |

### Privacy Guarantees

| Hidden | Revealed | Why |
|--------|----------|-----|
| Sender identity | Recipient address | Recipient must receive funds |
| Operator identity | Transaction amount | Required for accounting |
| KYC level | Nullifier | Prevents double-spending |

### Comparison to Traditional Approaches

| Approach | Privacy | Compliance | Verification |
|----------|---------|------------|--------------|
| Traditional KYC | None | Manual audit | Trust-based |
| Privacy coins | Full | None | N/A |
| **Bermuda POC** | **Selective** | **Cryptographic** | **Formal proofs** |

---

## Architecture

```
contracts/
├── registries/
│   ├── OperatorRegistry.sol      # Licensed operator management
│   └── KYCRegistry.sol           # KYC level attestations
├── ShieldedPool.sol              # Note commitments and nullifiers
└── verifiers/
    └── ComplianceVerifier.sol    # ZK proof verification

circuits/
├── membership.circom             # Merkle membership proofs
├── compliance.circom             # Compliance + nullifier circuit
└── lib/
    └── poseidon.circom           # Poseidon hash

lean/
└── BermudaVerification/
    ├── CCI/
    │   └── Core.lean             # Core compliance interface
    ├── Contracts/
    │   ├── Spec.lean             # Contract specifications
    │   └── Model.lean            # State machine model
    └── BermudaCompliance/
        ├── Spec.lean             # Compliance definitions
        ├── Model.lean            # State transitions
        └── Proofs.lean           # Security theorems
```

---

## Quick Start

### Prerequisites

- Node.js 18+
- Lean 4.17.0 (via [elan](https://github.com/leanprover/elan))
- Circom 2.x (for circuit compilation)

### Installation

```bash
# Install JS dependencies
npm install

# Compile Solidity
npm run compile

# Compile circuits
npm run compile:circuits

# Generate verifiers
npm run build:verifiers

# Run tests
npx hardhat test
```

### Build Lean Proofs

```bash
cd lean
lake build
```

---

## References

- [Bermuda Monetary Authority Guidelines](https://www.bma.bm/)
- [Circom Documentation](https://docs.circom.io/)
- [Lean 4 Documentation](https://leanprover.github.io/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)

---

## License

This project is licensed under the [Apoth3osis License Stack v1](LICENSE.md).

**Licensor:** Equation Capital LLC DBA Apoth3osis
**Contact:** rgoodman@apoth3osis.io

See [`licenses/`](licenses/) for the complete license texts:
- [Public Good License](licenses/Apoth3osis-Public-Good-License-1.0.md)
- [Small Business License](licenses/Apoth3osis-Small-Business-License-1.0.md)
- [Enterprise Commercial License](licenses/Apoth3osis-Enterprise-Commercial-License-1.0.md)
- [Certified Trademark License](licenses/Apoth3osis-Certified-Trademark-License-1.0.md)

---

<sub>Part of the <a href="https://github.com/apoth3osis/HeytingLean">HeytingLean</a> formal verification ecosystem.<br>
<a href="https://apoth3osis.io">apoth3osis.io</a></sub>
