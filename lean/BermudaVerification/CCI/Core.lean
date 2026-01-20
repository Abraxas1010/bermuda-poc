import Lean.Data.Json

/-!
# CCI Core — minimal canonical IR (v1)

Closed, nucleus‑passed expressions and opaque lens payloads for export/check.
This is intentionally small and opinionated to keep the checker trivial.
-/

namespace BermudaVerification
namespace CCI

abbrev Digest := ByteArray
abbrev AtomId := String

inductive Expr
  | atom (id : AtomId)
  | andR (a b : Expr)
  | orR  (a b : Expr)
  | impR (a b : Expr)
  | notR (a : Expr)
  deriving Repr, DecidableEq

def top : Expr := .atom "⊤"
def bot : Expr := .atom "⊥"

structure Lens where
  name  : String
  value : String   -- opaque payload (e.g., JSON-serialized elsewhere)
  deriving Repr, DecidableEq

end CCI
end BermudaVerification
