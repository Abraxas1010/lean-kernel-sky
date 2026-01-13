import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Bauer.ScottReflexiveDomain

/-!
# Eigenform → Combinator bridge (Church–Curry / Kauffman)

This module is the **Phase 2** “explicit bridge” for the generative stack:

* syntactic SKY re-entry: `Y f ↦ f (Y f)` (one-step rewrite)
* Scott-style fixed points: `scottFix f` satisfies `f (scottFix f) = scottFix f`

The key claim recorded here is **behavioral**: both are fixed-point mechanisms, living on
different carriers:

* `Comb` is a tiny SK(Y) syntax with a rewrite relation `Comb.Step/Steps`.
* `scottFix` lives in domain theory (`ReflexiveDomain`) for Scott-continuous endomaps.

We do *not* assert a typed interpretation of combinators into a particular domain here (that
would require a full denotational semantics layer). Instead we:

1) prove the canonical “eigenform unfolding” lemma for `Y` in the SKY rewrite system;
2) implement Curry’s “gremlin”/duplication trick and prove `G(G) →* f (G(G))`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace EigenformBridge

open Comb

/-! ## Small-step / multi-step helpers -/

private theorem steps_transitive {t u v : Comb} : Steps t u → Steps u v → Steps t v := by
  intro htu huv
  induction htu with
  | refl _ => simpa using huv
  | trans hstep hsteps ih => exact Steps.trans hstep (ih huv)

theorem Steps.app_left {f f' a : Comb} : Steps f f' → Steps (Comb.app f a) (Comb.app f' a) := by
  intro h
  induction h with
  | refl t => exact Steps.refl (Comb.app t a)
  | trans hstep hsteps ih =>
      exact Steps.trans (Step.app_left hstep) ih

theorem Steps.app_right {f a a' : Comb} : Steps a a' → Steps (Comb.app f a) (Comb.app f a') := by
  intro h
  induction h with
  | refl t => exact Steps.refl (Comb.app f t)
  | trans hstep hsteps ih =>
      exact Steps.trans (Step.app_right hstep) ih

/-! ## Y as an eigenform rule -/

/-- One-step Y-unfolding: `Y f ↦ f (Y f)`. -/
theorem Y_step (f : Comb) :
    Step (Comb.app .Y f) (Comb.app f (Comb.app .Y f)) := by
  simpa using Step.Y_rule (f := f)

/-- Multi-step Y-unfolding as an eigenform equation. -/
theorem Y_eigenform (f : Comb) :
    Steps (Comb.app .Y f) (Comb.app f (Comb.app .Y f)) := by
  exact Steps.trans (Y_step f) (Steps.refl _)

/-- Joinability statement: `Y f` and `f (Y f)` share a common reduct (namely `f (Y f)`). -/
theorem Y_produces_fixedpoint (f : Comb) :
    ∃ t : Comb, Steps (Comb.app .Y f) t ∧ Steps (Comb.app f (Comb.app .Y f)) t := by
  refine ⟨Comb.app f (Comb.app .Y f), ?_, ?_⟩
  · exact Y_eigenform f
  · exact Steps.refl _

/-! ## Curry’s duplication / gremlin construction -/

/-- The ω combinator (self-application): `ω := S I I`. -/
def omega : Comb :=
  Comb.app (Comb.app .S Comb.I) Comb.I

/-- `ω t →* t t`. -/
theorem omega_selfApply (t : Comb) :
    Steps (Comb.app omega t) (Comb.app t t) := by
  -- `ω t = (S I I) t ↦ I t (I t) →* t t`.
  have h1 :
      Step (Comb.app omega t) (Comb.app (Comb.app Comb.I t) (Comb.app Comb.I t)) := by
    -- S-rule with `x = I`, `y = I`, `z = t`.
    simpa [omega] using Step.S_rule (x := Comb.I) (y := Comb.I) (z := t)
  have hIt : Steps (Comb.app Comb.I t) t := Comb.I_reduces t
  have h2 : Steps (Comb.app (Comb.app Comb.I t) (Comb.app Comb.I t)) (Comb.app t t) := by
    -- Reduce both occurrences of `I t` to `t`.
    have hLeft : Steps (Comb.app (Comb.app Comb.I t) (Comb.app Comb.I t)) (Comb.app t (Comb.app Comb.I t)) :=
      Steps.app_left (a := Comb.app Comb.I t) hIt
    have hRight : Steps (Comb.app t (Comb.app Comb.I t)) (Comb.app t t) :=
      Steps.app_right (f := t) hIt
    exact steps_transitive hLeft hRight
  exact Steps.trans h1 h2

/-- The “gremlin” `G` for `f`: `G := S (K f) ω`. Then `G x →* f (x x)`. -/
def gremlin (f : Comb) : Comb :=
  Comb.app (Comb.app .S (Comb.app .K f)) omega

/-- `G x →* f (x x)` where `G := gremlin f`. -/
theorem gremlin_apply (f x : Comb) :
    Steps (Comb.app (gremlin f) x) (Comb.app f (Comb.app x x)) := by
  -- `(S (K f) ω) x ↦ (K f x) (ω x) ↦ f (ω x) →* f (x x)`.
  have hS :
      Step (Comb.app (gremlin f) x)
        (Comb.app (Comb.app (Comb.app .K f) x) (Comb.app omega x)) := by
    simpa [gremlin] using Step.S_rule (x := Comb.app .K f) (y := omega) (z := x)
  have hK :
      Step (Comb.app (Comb.app (Comb.app .K f) x) (Comb.app omega x))
        (Comb.app f (Comb.app omega x)) := by
    -- Step in function position: `(K f x) ↦ f`.
    exact Step.app_left (Step.K_rule (x := f) (y := x))
  have hω : Steps (Comb.app omega x) (Comb.app x x) := omega_selfApply x
  have hLift : Steps (Comb.app f (Comb.app omega x)) (Comb.app f (Comb.app x x)) :=
    Steps.app_right (f := f) hω
  exact steps_transitive (Steps.trans hS (Steps.trans hK (Steps.refl _))) hLift

/-- Fixed-point theorem (syntactic): `G(G) →* f (G(G))` for `G := gremlin f`. -/
theorem gremlin_fixedpoint (f : Comb) :
    Steps (Comb.app (gremlin f) (gremlin f)) (Comb.app f (Comb.app (gremlin f) (gremlin f))) := by
  -- `G G →* f (G G)` is exactly `gremlin_apply f (gremlin f)` plus one ω-step.
  -- `gremlin_apply` gives `G G →* f (G G)` already (since `x = G`).
  simpa using gremlin_apply (f := f) (x := gremlin f)

/-! ## Scott fixed point recap (domain-theoretic side) -/

namespace Bauer

open HeytingLean.LoF.Bauer

theorem scottFix_isFixed' {α : Type _} [OmegaCompletePartialOrder α] [OrderBot α] (f : α →𝒄 α) :
    f (HeytingLean.LoF.Bauer.scottFix (α := α) f) = HeytingLean.LoF.Bauer.scottFix (α := α) f :=
  HeytingLean.LoF.Bauer.scottFix_isFixed (α := α) (f := f)

/-!
`scottFix` is already provided in `HeytingLean.LoF.Bauer.ScottReflexiveDomain`:

* `scottFix : (α →𝒄 α) → α`
* `scottFix_isFixed : f (scottFix f) = scottFix f`

This module does not re-prove domain theory; it records the bridge pattern:
SKY’s `Y`-unfolding and Scott’s `scottFix` are both fixed-point/eigenform operators.
-/

end Bauer

end EigenformBridge

end Combinators
end LoF
end HeytingLean
