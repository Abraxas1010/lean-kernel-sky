import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Order.CompleteBooleanAlgebra

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory
open Order

universe v u

variable {C : Type u} [Category.{v} C]

/-!
# `Sieve X` is a frame

Sieves on a fixed object `X` form a complete lattice (in mathlib). Since meet is intersection and
`sSup` is (generated) union, finite meets distribute over arbitrary joins. We package the minimal
axioms into `Order.Frame.MinimalAxioms` and let `Order.Frame.ofMinimalAxioms` construct the
canonical Heyting implication and complement.
-/

instance sieveFrameMinimalAxioms (X : C) : Order.Frame.MinimalAxioms (Sieve X) where
  __ := (inferInstance : CompleteLattice (Sieve X))
  inf_sSup_le_iSup_inf a s := by
    intro Y f haf
    rcases haf with ⟨ha, hs⟩
    rcases hs with ⟨b, hb, hbmem⟩
    have hle : a ⊓ b ≤ ⨆ b ∈ s, a ⊓ b := by
      refine le_iSup_of_le b ?_
      refine le_iSup_of_le hb ?_
      exact le_rfl
    exact hle f ⟨ha, hbmem⟩

noncomputable instance sieveFrame (X : C) : Order.Frame (Sieve X) :=
  Order.Frame.ofMinimalAxioms (minAx := sieveFrameMinimalAxioms (C := C) X)

end Topos
end Combinators
end LoF
end HeytingLean

