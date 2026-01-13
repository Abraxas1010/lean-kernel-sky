import HeytingLean.LoF.Combinators.Heyting.FixedPoints

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Heyting

open Order

universe u

/-!
# Fixed points as a (complete) Heyting algebra

For a nucleus `n : Order.Nucleus α`, the fixed points `{x | n x = x}` coincide with the range of `n`.

When the ambient order is a frame (`Order.Frame α`, i.e. a complete Heyting algebra), mathlib equips
`Set.range n` with a canonical `Order.Frame` structure. This is the standard “sublocale” result:
stable elements form a frame, hence a bundled Heyting algebra.
-/

/-- Fixed points `{x | n x = x}` are exactly the range of `n` (as a set). -/
theorem fixedPoints_eq_range {α : Type u} [SemilatticeInf α] (n : Nucleus α) :
    (Ω_ n) = Set.range (fun x => n x) := by
  ext x
  constructor
  · intro hx
    exact ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    simp

/-- The stable elements of a nucleus as a bundled type (subtype of the range). -/
abbrev FixedPointType {α : Type u} [SemilatticeInf α] (n : Nucleus α) : Type u :=
  Set.range (fun x => n x)

/-- Any element of the range of a nucleus satisfies the fixed point equation. -/
@[simp] theorem fixedPointType_apply {α : Type u} [SemilatticeInf α] (n : Nucleus α)
    (x : FixedPointType n) : n x.1 = x.1 := by
  rcases x.2 with ⟨y, hy⟩
  calc
    n x.1 = n (n y) := by simp [hy]
    _ = n y := by simp
    _ = x.1 := hy

/-- If the ambient order is a frame, then the stable elements form a frame (complete Heyting algebra). -/
def fixedPointType_instFrame {α : Type u} [Order.Frame α] (n : Nucleus α) :
    Order.Frame (FixedPointType n) := by
  infer_instance

/-- In particular, stable elements inherit a bundled Heyting algebra structure. -/
def fixedPointType_instHeyting {α : Type u} [Order.Frame α] (n : Nucleus α) :
    HeytingAlgebra (FixedPointType n) := by
  infer_instance

end Heyting
end Combinators
end LoF
end HeytingLean

