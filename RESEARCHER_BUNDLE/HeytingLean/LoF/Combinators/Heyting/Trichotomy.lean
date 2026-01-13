import HeytingLean.LoF.Combinators.Heyting.CombinatorMap
import HeytingLean.LoF.Combinators.Heyting.FixedPoints
import HeytingLean.LoF.Combinators.Heyting.Stability

/-!
# Two unstable operations, one constructive impossibility

This module packages the "2-unstable / 1-impossible" slogan into precise Lean theorems.

*Unstable* means: there exists a nucleus `n` and fixed points `a,b ∈ Ωₙ` such that the raw
operation takes you outside `Ωₙ`. The corresponding *closed* operation (apply the nucleus)
always lands back in `Ωₙ`.

*Impossible* means: no total "fixed point operator" exists for an endomap with no fixed points
(constructively, without any metatheory about normalization).
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Heyting

open Order

/-! ## A constructive "no fixed point combinator" lemma -/

/-- If `f : α → α` has no fixed points, then no total fixed-point operator `Y` can satisfy
`Y g = g (Y g)` for *all* `g : α → α`. -/
theorem no_fixedPointOperator_of_noFixedPoint {α : Type u} (f : α → α)
    (hf : ∀ a : α, f a ≠ a) :
    ¬ ∃ Y : (α → α) → α, ∀ g : α → α, Y g = g (Y g) := by
  rintro ⟨Y, hY⟩
  have h : Y f = f (Y f) := hY f
  have hfix : f (Y f) = Y f := h.symm
  exact (hf (Y f)) hfix

private theorem bool_not_noFixedPoint : ∀ b : Bool, Bool.not b ≠ b := by
  intro b
  cases b <;> decide

/-- Concrete instance: there is no total fixed-point operator on `Bool`
because `Bool.not` has no fixed point. -/
theorem no_fixedPointOperator_bool :
    ¬ ∃ Y : (Bool → Bool) → Bool, ∀ f : Bool → Bool, Y f = f (Y f) := by
  refine no_fixedPointOperator_of_noFixedPoint (α := Bool) Bool.not ?_
  exact bool_not_noFixedPoint

/-! ## The two instability witnesses (joins, complements) -/

theorem sup_unstable_witness :
    Unstable Examples.FiveElemJoin.nucleus Examples.FiveElemJoin.sup :=
  Examples.FiveElemJoin.sup_unstable

theorem compl_unstable_witness :
    Unstable Examples.TwoElemCompl.nucleus (fun a _ => Examples.TwoElemCompl.compl a) :=
  Examples.TwoElemCompl.compl_unstable

/-! ## The packaged “2 unstable + 1 impossible” statement -/

theorem heyting_trichotomy :
    Unstable Examples.FiveElemJoin.nucleus Examples.FiveElemJoin.sup ∧
      Unstable Examples.TwoElemCompl.nucleus (fun a _ => Examples.TwoElemCompl.compl a) ∧
      (¬ ∃ Y : (Bool → Bool) → Bool, ∀ f : Bool → Bool, Y f = f (Y f)) := by
  exact ⟨sup_unstable_witness, compl_unstable_witness, no_fixedPointOperator_bool⟩

/-- Sanity check: the stated LoF ↔ SKY tag mapping. -/
theorem lof_correspondence :
    combToLoF (HeytingLean.LoF.Comb.K) = some LoFPrimitive.unmark ∧
      combToLoF (HeytingLean.LoF.Comb.S) = some LoFPrimitive.mark ∧
      combToLoF (HeytingLean.LoF.Comb.Y) = some LoFPrimitive.reentry := by
  simp [combToLoF]

end Heyting
end Combinators
end LoF
end HeytingLean

