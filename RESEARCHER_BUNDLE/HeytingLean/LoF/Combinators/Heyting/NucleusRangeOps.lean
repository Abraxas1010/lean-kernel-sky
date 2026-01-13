import Mathlib.Order.Nucleus

/-!
# NucleusRangeOps — Heyting operations on the range of a nucleus

This module records small but high-value “operation compatibility” lemmas for the type
`Set.range n` (the range of a nucleus `n : Nucleus α`) when the ambient order is a frame.

The key fact used later in the SKY/LoF/topos correspondence is that **Heyting implication in the
range** agrees with the **ambient** Heyting implication after coercion.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Heyting

open Order

universe u

variable {α : Type u} [Order.Frame α]

namespace Nucleus

variable (n : Nucleus α)

/-- In the range `Set.range n`, Heyting implication agrees with the ambient implication after coercion. -/
theorem coe_himp (a b : Set.range n) : ((a ⇨ b : Set.range n) : α) = (a : α) ⇨ (b : α) := by
  apply le_antisymm
  · refine (le_himp_iff).2 ?_
    have hrange : (a ⇨ b : Set.range n) ⊓ a ≤ b := by
      have hEq : (a ⇨ b : Set.range n) ⊓ a = b ⊓ a :=
        himp_inf_self (a := a) (b := b)
      rw [hEq]
      exact inf_le_left
    exact (show ((a ⇨ b : Set.range n) : α) ⊓ (a : α) ≤ (b : α) from hrange)
  ·
    have hx_mem : (a : α) ⇨ (b : α) ∈ Set.range n := by
      have hb : n (b : α) = (b : α) := (Nucleus.mem_range).1 b.2
      have : n ((a : α) ⇨ (b : α)) = (a : α) ⇨ (b : α) := by
        simpa [hb] using (Nucleus.map_himp_apply (n := n) (x := (a : α)) (y := (b : α)))
      exact (Nucleus.mem_range).2 this
    let x : Set.range n := ⟨(a : α) ⇨ (b : α), hx_mem⟩
    have hx_le : x ≤ (a ⇨ b : Set.range n) := by
      refine (le_himp_iff).2 ?_
      have : ((x : α) ⊓ (a : α)) ≤ (b : α) := by
        have hEq : ((a : α) ⇨ (b : α)) ⊓ (a : α) = (b : α) ⊓ (a : α) :=
          himp_inf_self (a := (a : α)) (b := (b : α))
        have h : ((a : α) ⇨ (b : α)) ⊓ (a : α) ≤ (b : α) := by
          rw [hEq]
          exact inf_le_left
        change (((a : α) ⇨ (b : α)) ⊓ (a : α)) ≤ (b : α)
        exact h
      exact this
    have : (x : α) ≤ ((a ⇨ b : Set.range n) : α) := hx_le
    simpa [x] using this

end Nucleus

end Heyting
end Combinators
end LoF
end HeytingLean

