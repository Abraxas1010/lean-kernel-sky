import Mathlib.Order.Heyting.Basic
import HeytingLean.LoF.Combinators.Heyting.Nucleus

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Heyting

open Order

variable {α : Type u} [HeytingAlgebra α]

variable (n : Nucleus α)

/-- Closed join operation on the ambient Heyting algebra. -/
def closedSup (a b : α) : α := n (a ⊔ b)

/-- Closed negation operation on the ambient Heyting algebra. -/
def closedCompl (a : α) : α := n (aᶜ)

/-- Closed implication operation on the ambient Heyting algebra. -/
def closedHImp (a b : α) : α := n (a ⇨ b)

@[simp] theorem closedSup_mem (a b : α) : closedSup n a b ∈ Ω_ n := by
  simp [closedSup, FixedPoints, Nucleus.idempotent]

@[simp] theorem closedCompl_mem (a : α) : closedCompl n a ∈ Ω_ n := by
  simp [closedCompl, FixedPoints, Nucleus.idempotent]

@[simp] theorem closedHImp_mem (a b : α) : closedHImp n a b ∈ Ω_ n := by
  simp [closedHImp, FixedPoints, Nucleus.idempotent]

end Heyting
end Combinators
end LoF
end HeytingLean

