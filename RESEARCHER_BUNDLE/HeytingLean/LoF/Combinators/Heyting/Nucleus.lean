import Mathlib.Order.Nucleus

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Heyting

open Order

/-- Fixed points of a nucleus `n` (the stable elements). -/
def FixedPoints {α : Type u} [SemilatticeInf α] (n : Nucleus α) : Set α :=
  {x | n x = x}

notation "Ω_" n => FixedPoints n

@[simp] theorem mem_fixedPoints_iff {α : Type u} [SemilatticeInf α] (n : Nucleus α) (x : α) :
    (x ∈ Ω_ n) ↔ n x = x := Iff.rfl

/-- Fixed points are closed under `⊓` (because nuclei preserve `inf`). -/
theorem fixed_inf_closed {α : Type u} [SemilatticeInf α] (n : Nucleus α) (a b : α)
    (ha : a ∈ Ω_ n) (hb : b ∈ Ω_ n) : a ⊓ b ∈ Ω_ n := by
  simp [FixedPoints] at ha hb ⊢
  simp [ha, hb]

end Heyting
end Combinators
end LoF
end HeytingLean

