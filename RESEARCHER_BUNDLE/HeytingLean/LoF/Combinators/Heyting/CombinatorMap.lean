import HeytingLean.LoF.Combinators.SKY

/-!
# SKY ↔ LoF primitive correspondence

This file records a *syntactic* correspondence between SKY combinators and
Laws of Form primitives (as tags), and exposes the defining one-step rewrite
rules as named lemmas.

The main mathematical content of the SKY slice lives in the nucleus/Heyting
and topos layers; this file exists so downstream narrative can reference the
mapping and rules unambiguously.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Heyting

/-! ## LoF primitive tags -/

inductive LoFPrimitive
  | mark
  | unmark
  | reentry
  deriving DecidableEq, Repr

/-- A partial map from SKY syntax to LoF primitive tags.

`Comb.app _ _` is not a primitive, so it maps to `none`.
-/
def combToLoF : HeytingLean.LoF.Comb → Option LoFPrimitive
  | .K => some .unmark
  | .S => some .mark
  | .Y => some .reentry
  | .app _ _ => none

@[simp] theorem combToLoF_K : combToLoF (HeytingLean.LoF.Comb.K) = some .unmark := rfl
@[simp] theorem combToLoF_S : combToLoF (HeytingLean.LoF.Comb.S) = some .mark := rfl
@[simp] theorem combToLoF_Y : combToLoF (HeytingLean.LoF.Comb.Y) = some .reentry := rfl

/-! ## Named one-step reductions -/

open HeytingLean.LoF

/-- `K x y ↦ x` (projection / forgetful rule). -/
theorem K_step (x y : Comb) :
    Comb.Step (Comb.app (Comb.app .K x) y) x := by
  simpa using Comb.Step.K_rule (x := x) (y := y)

/-- `S x y z ↦ x z (y z)` (distribution rule). -/
theorem S_step (x y z : Comb) :
    Comb.Step (Comb.app (Comb.app (Comb.app .S x) y) z)
      (Comb.app (Comb.app x z) (Comb.app y z)) := by
  simpa using Comb.Step.S_rule (x := x) (y := y) (z := z)

/-- `Y f ↦ f (Y f)` (re-entry / fixed-point unfolding rule). -/
theorem Y_step (f : Comb) :
    Comb.Step (Comb.app .Y f) (Comb.app f (Comb.app .Y f)) := by
  simpa using Comb.Step.Y_rule (f := f)

end Heyting
end Combinators
end LoF
end HeytingLean

