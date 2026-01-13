import HeytingLean.LoF.Combinators.Heyting.Nucleus

/-!
# Stability / instability witnesses for nuclei fixed points

This file provides:

* `Stable n op`: `op` preserves membership in the fixed-point set `Ωₙ`.
* `Unstable n op`: there exist fixed points that are sent outside `Ωₙ` by `op`.

It also includes concrete instability witnesses used by `Heyting.Trichotomy`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Heyting

open Order

/-! ## Generic stability predicates -/

/-- An operation is stable if it preserves membership in `Ωₙ` without applying the nucleus. -/
def Stable {α : Type u} [SemilatticeInf α] (n : Nucleus α) (op : α → α → α) : Prop :=
  ∀ a b, (a ∈ Ω_ n) → (b ∈ Ω_ n) → (op a b ∈ Ω_ n)

/-- An operation is unstable if there are fixed points that it sends outside `Ωₙ`. -/
def Unstable {α : Type u} [SemilatticeInf α] (n : Nucleus α) (op : α → α → α) : Prop :=
  ∃ a b, (a ∈ Ω_ n) ∧ (b ∈ Ω_ n) ∧ (op a b ∉ Ω_ n)

/-- `⊓` is stable for any nucleus because nuclei preserve `inf`. -/
theorem inf_stable {α : Type u} [SemilatticeInf α] (n : Nucleus α) : Stable n (· ⊓ ·) := by
  intro a b ha hb
  exact fixed_inf_closed n a b ha hb

/-! ## Concrete witnesses (used by the paper narrative) -/

namespace Examples

/-! ### Join instability on a finite "lower-set" lattice -/

namespace FiveElemJoin

/-- A 5-element lattice encoding the lower sets of the poset `a,b ≤ c`:
`⊥, {a}, {b}, {a,b}, {a,b,c}`. -/
inductive L5
  | bot | a | b | ab | top
  deriving DecidableEq, Repr

open L5

instance : LE L5 where
  le x y :=
    match x, y with
    | bot, _ => True
    | a, a => True
    | b, b => True
    | ab, ab => True
    | top, top => True
    | a, ab => True
    | b, ab => True
    | a, top => True
    | b, top => True
    | ab, top => True
    | _, _ => False

instance : DecidableRel ((· ≤ ·) : L5 → L5 → Prop) := by
  intro x y
  cases x <;> cases y <;> simp [LE.le] <;> infer_instance

instance : Preorder L5 where
  le := (· ≤ ·)
  lt := fun x y => x ≤ y ∧ ¬ y ≤ x
  le_refl x := by cases x <;> simp [LE.le]
  le_trans x y z := by
    cases x <;> cases y <;> cases z <;> simp [LE.le]

instance : PartialOrder L5 :=
  { instPreorderL5 with
    le_antisymm := by
      intro x y hxy hyx
      cases x <;> cases y <;> simp [LE.le] at hxy hyx <;> cases hxy <;> cases hyx <;> rfl }

def inf : L5 → L5 → L5
  | bot, _ => bot
  | _, bot => bot
  | top, x => x
  | x, top => x
  | a, a => a
  | b, b => b
  | ab, ab => ab
  | a, ab => a
  | ab, a => a
  | b, ab => b
  | ab, b => b
  | a, b => bot
  | b, a => bot

instance : SemilatticeInf L5 where
  inf := inf
  inf_le_left := by
    intro x y
    cases x <;> cases y <;> simp [inf, LE.le]
  inf_le_right := by
    intro x y
    cases x <;> cases y <;> simp [inf, LE.le]
  le_inf := by
    intro x y z hxy hxz
    cases x <;> cases y <;> cases z <;> simp [inf, LE.le] at hxy hxz ⊢
  toPartialOrder := instPartialOrderL5

def sup : L5 → L5 → L5
  | bot, x => x
  | x, bot => x
  | top, _ => top
  | _, top => top
  | a, a => a
  | b, b => b
  | ab, ab => ab
  | a, b => ab
  | b, a => ab
  | a, ab => ab
  | ab, a => ab
  | b, ab => ab
  | ab, b => ab

def close : L5 → L5
  | ab => top
  | x => x

noncomputable def nucleus : Nucleus L5 :=
  Nucleus.mk
    (toInfHom :=
      { toFun := close
        map_inf' := by
          intro x y
          cases x <;> cases y <;> rfl })
    (idempotent' := by
      intro x
      cases x <;> simp [close, LE.le])
    (le_apply' := by
      intro x
      cases x <;> simp [close, LE.le])

theorem sup_unstable : Unstable nucleus sup := by
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simp [FixedPoints, nucleus, close]
  · simp [FixedPoints, nucleus, close]
  · simp [FixedPoints, nucleus, close, sup]

end FiveElemJoin

/-! ### Complement instability on a two-element lattice -/

namespace TwoElemCompl

inductive B2
  | f | t
  deriving DecidableEq, Repr

open B2

instance : LE B2 where
  le x y :=
    match x, y with
    | f, _ => True
    | t, t => True
    | _, _ => False

instance : DecidableRel ((· ≤ ·) : B2 → B2 → Prop) := by
  intro x y
  cases x <;> cases y <;> simp [LE.le] <;> infer_instance

instance : Preorder B2 where
  le := (· ≤ ·)
  lt := fun x y => x ≤ y ∧ ¬ y ≤ x
  le_refl x := by cases x <;> simp [LE.le]
  le_trans x y z := by
    cases x <;> cases y <;> cases z <;> simp [LE.le]

instance : PartialOrder B2 :=
  { instPreorderB2 with
    le_antisymm := by
      intro x y hxy hyx
      cases x <;> cases y <;> simp [LE.le] at hxy hyx <;> cases hxy <;> cases hyx <;> rfl }

def inf : B2 → B2 → B2
  | f, _ => f
  | _, f => f
  | t, t => t

instance : SemilatticeInf B2 where
  inf := inf
  inf_le_left := by
    intro x y
    cases x <;> cases y <;> simp [inf, LE.le]
  inf_le_right := by
    intro x y
    cases x <;> cases y <;> simp [inf, LE.le]
  le_inf := by
    intro x y z hxy hxz
    cases x <;> cases y <;> cases z <;> simp [inf, LE.le] at hxy hxz ⊢
  toPartialOrder := instPartialOrderB2

def compl : B2 → B2
  | f => t
  | t => f

def close (_b : B2) : B2 := t

noncomputable def nucleus : Nucleus B2 :=
  Nucleus.mk
    (toInfHom :=
      { toFun := close
        map_inf' := by
          intro x y
          cases x <;> cases y <;> rfl })
    (idempotent' := by
      intro x
      cases x <;> simp [close, LE.le])
    (le_apply' := by
      intro x
      cases x <;> simp [close, LE.le])

theorem compl_unstable : Unstable nucleus (fun a _ => compl a) := by
  refine ⟨t, t, ?_, ?_, ?_⟩
  · show nucleus t = t
    rfl
  · show nucleus t = t
    rfl
  · intro h
    simp [nucleus, close, compl] at h

end TwoElemCompl

end Examples

end Heyting
end Combinators
end LoF
end HeytingLean

