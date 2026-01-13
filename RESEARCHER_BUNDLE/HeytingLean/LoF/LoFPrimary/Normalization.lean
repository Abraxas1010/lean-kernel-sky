import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter
import HeytingLean.LoF.LoFPrimary.Rewrite

/-!
# LoFPrimary.Normalization — semantics + canonicalization by truth sets

We interpret primary LoF expressions in classical two-valued logic:

* `void`  ↦ `False`
* `mark`  ↦ Boolean negation
* `juxt`  ↦ Boolean disjunction

This provides:

* a semantics `eval : Expr n → (Fin n → Bool) → Bool`;
* a **canonicalization** `trueSet : Expr n → Finset (Fin n → Bool)` recording exactly the
  valuations where the expression evaluates to `true`;
* a decidable equivalence `Eqv A B :↔ trueSet A = trueSet B`;
* soundness: one-step and multi-step rewriting preserves this semantics.

This is a mathematically strong “primary algebra” baseline: it gives a complete decision procedure
for equivalence of primary expressions with finitely many variables (via finite truth sets).

Re-entry / second-degree equations are *not* handled here; see `HeytingLean.LoF.LoFSecond` for a
conservative extension with an explicit re-entry constant and a 3-valued semantics.
-/

namespace HeytingLean
namespace LoF
namespace LoFPrimary

open Expr

variable {n : Nat}

/-! ## Semantics -/

def eval : Expr n → (Fin n → Bool) → Bool
  | .void, _ => false
  | .var i, ρ => ρ i
  | .mark A, ρ => !(eval A ρ)
  | .juxt A B, ρ => eval A ρ || eval B ρ

/-! ## Canonicalization -/

/-- Canonical truth-set representation of an expression. -/
def trueSet (A : Expr n) : Finset (Fin n → Bool) :=
  Finset.filter (fun ρ => eval A ρ = true) Finset.univ

@[simp] theorem mem_trueSet {A : Expr n} {ρ : Fin n → Bool} :
    ρ ∈ trueSet (n := n) A ↔ eval A ρ = true := by
  simp [trueSet]

/-! ## Semantic equivalence -/

/-- Pointwise semantic equivalence. -/
def Eqv (A B : Expr n) : Prop :=
  ∀ ρ : Fin n → Bool, eval A ρ = eval B ρ

theorem eqv_iff_trueSet_eq {A B : Expr n} :
    Eqv (n := n) A B ↔ trueSet (n := n) A = trueSet (n := n) B := by
  constructor
  · intro h
    ext ρ
    simp [trueSet, h ρ]
  · intro h ρ
    have hmem : (eval A ρ = true) ↔ (eval B ρ = true) := by
      have : ρ ∈ trueSet (n := n) A ↔ ρ ∈ trueSet (n := n) B := by
        simp [h]
      simpa [mem_trueSet] using this
    cases hA : eval A ρ <;> cases hB : eval B ρ <;> try rfl
    · -- `eval A ρ = false`, `eval B ρ = true`
      have : eval A ρ = true := (hmem.mpr hB)
      simp [hA] at this
    · -- `eval A ρ = true`, `eval B ρ = false`
      have : eval B ρ = true := (hmem.mp hA)
      simp [hB] at this

/-! ## Soundness of the rewrite rules -/

theorem step_sound {A B : Expr n} : Step A B → Eqv (n := n) A B := by
  intro h ρ
  induction h with
  | calling A =>
      simp [eval, Bool.or_self]
  | crossing A =>
      simp [eval]
  | void_left A =>
      simp [eval]
  | void_right A =>
      simp [eval]
  | juxt_left _ ih =>
      simp [eval, ih]
  | juxt_right _ ih =>
      simp [eval, ih]
  | mark_congr _ ih =>
      simp [eval, ih]

theorem steps_sound {A B : Expr n} : Steps A B → Eqv (n := n) A B := by
  intro h
  induction h with
  | refl A =>
      intro ρ
      rfl
  | trans hstep hsteps ih =>
      intro ρ
      exact (step_sound (n := n) hstep ρ).trans (ih ρ)

end LoFPrimary
end LoF
end HeytingLean
