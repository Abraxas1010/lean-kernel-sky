import HeytingLean.LoF.LoFPrimary.Syntax

/-!
# LoFPrimary.Rewrite — calling/crossing as a rewrite relation

We orient the primary algebra equalities as simplification rules:

* **calling**  : `A A ↦ A`
* **crossing** : `mark (mark A) ↦ A`

and propagate them through contexts (`mark`, `juxt`).

This is intentionally conservative: we do **not** attempt to encode the full equational theory
(commutativity/associativity of juxtaposition, etc.) as rewrites here.  Those are handled at the
semantic/canonicalization layer in `LoFPrimary.Normalization`.
-/

namespace HeytingLean
namespace LoF
namespace LoFPrimary

open Expr

variable {n : Nat}

/-! ## One-step reduction -/

inductive Step : Expr n → Expr n → Prop where
  | calling (A : Expr n) : Step (Expr.juxt A A) A
  | crossing (A : Expr n) : Step (Expr.mark (Expr.mark A)) A
  | void_left (A : Expr n) : Step (Expr.juxt Expr.void A) A
  | void_right (A : Expr n) : Step (Expr.juxt A Expr.void) A
  | juxt_left {A A' B : Expr n} : Step A A' → Step (Expr.juxt A B) (Expr.juxt A' B)
  | juxt_right {A B B' : Expr n} : Step B B' → Step (Expr.juxt A B) (Expr.juxt A B')
  | mark_congr {A A' : Expr n} : Step A A' → Step (Expr.mark A) (Expr.mark A')

/-! ## Reflexive-transitive closure -/

inductive Steps : Expr n → Expr n → Prop where
  | refl (A : Expr n) : Steps A A
  | trans {A B C : Expr n} : Step A B → Steps B C → Steps A C

namespace Steps

theorem transitive {A B C : Expr n} : Steps A B → Steps B C → Steps A C := by
  intro hAB hBC
  induction hAB with
  | refl _ =>
      simpa using hBC
  | trans hstep hsteps ih =>
      exact Steps.trans hstep (ih hBC)

end Steps

end LoFPrimary
end LoF
end HeytingLean

