import Lake
open Lake DSL

package BermudaVerification where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib BermudaVerification where
  roots := #[`BermudaVerification.CCI.Core,
             `BermudaVerification.Contracts.Spec,
             `BermudaVerification.Contracts.Model,
             `BermudaVerification.BermudaCompliance.Spec,
             `BermudaVerification.BermudaCompliance.Model,
             `BermudaVerification.BermudaCompliance.Proofs]
