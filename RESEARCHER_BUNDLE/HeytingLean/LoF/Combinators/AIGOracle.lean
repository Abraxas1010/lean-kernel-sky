import HeytingLean.LoF.LoFPrimary.AIG

/-!
# AIGOracle — packaged AIG-backed boolean oracle references

This module packages the existing verified LoFPrimary → AIG compilation pipeline
(`HeytingLean.LoF.LoFPrimary.AIG`) into a reusable “oracle reference” carrying:

* a LoF expression `Expr n`
* a concrete Boolean environment `Fin n → Bool`

and exposes:

* `eval` — evaluate via the compiled AIG
* `eval_eq_lof_eval` — evaluation agrees with `LoFPrimary.eval`
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF.LoFPrimary

namespace AIGOracle

/-- A concrete oracle reference: an LoF expression together with its environment. -/
structure Ref (n : Nat) where
  expr : LoFPrimary.Expr n
  inputs : Fin n → Bool

/-- The compiled AIG for an oracle reference. -/
def graph {n : Nat} (r : Ref n) : LoFPrimary.AIG.Graph n :=
  LoFPrimary.AIG.ofMuxNet (LoFPrimary.MuxNet.toMuxNet (n := n) r.expr)

/-- Evaluate via the verified AIG backend. -/
def eval {n : Nat} (r : Ref n) : Bool :=
  (graph r).eval r.inputs

theorem eval_eq_lof_eval {n : Nat} (r : Ref n) :
    eval r = LoFPrimary.eval (n := n) r.expr r.inputs := by
  simp [eval, graph, LoFPrimary.AIG.loFToAIG_correct]

end AIGOracle

end Combinators
end LoF
end HeytingLean

