import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.SKYMultiway

/-!
# SKYExec — tiny fuel-limited evaluator for `Comb` (runtime support)

This module provides a deterministic one-step reducer (leftmost-outermost)
and a fuel-limited multi-step reducer for the `HeytingLean.LoF.Comb` syntax.

It is intended for lightweight executable demos and sanity checks; it is not a
verified normalizer.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace SKYExec

/-- Deterministic one-step SKY reduction (leftmost-outermost).

Implementation note: we reuse the already-verified one-step enumerator
`Comb.stepEdgesList` (from `SKYMultiway`) and pick its first edge.
-/
def step? (t : Comb) : Option Comb :=
  match Comb.stepEdgesList t with
  | [] => none
  | (_, u) :: _ => some u

/-- Reduce for at most `fuel` steps, stopping early at normal forms. -/
def reduceFuel : Nat → Comb → Comb
  | 0, t => t
  | Nat.succ n, t =>
      match step? t with
      | some t' => reduceFuel n t'
      | none => t

/-! ## Soundness w.r.t. the formal small-step semantics (`Comb.Step`) -/

theorem step?_sound : ∀ {t u : Comb}, step? t = some u → Comb.Step t u := by
  intro t u h
  cases hlist : Comb.stepEdgesList t with
  | nil =>
      simp [step?, hlist] at h
  | cons p ps =>
      rcases p with ⟨ed, u0⟩
      have h0 : step? t = some u0 := by
        simp [step?, hlist]
      have hu : u0 = u := Option.some.inj (h0.symm.trans h)
      have hmem : (ed, u0) ∈ Comb.stepEdgesList t := by
        simp [hlist]
      have hstep0 : Comb.Step t u0 :=
        Comb.stepEdgesList_sound (t := t) (ed := ed) (u := u0) hmem
      simpa [hu] using hstep0

theorem reduceFuel_sound (fuel : Nat) (t : Comb) : Comb.Steps t (reduceFuel fuel t) := by
  induction fuel generalizing t with
  | zero =>
      simp [reduceFuel, Comb.Steps.refl]
  | succ n ih =>
      cases hstep : step? t with
      | none =>
          simpa [reduceFuel, hstep] using (Comb.Steps.refl t)
      | some t' =>
          simpa [reduceFuel, hstep] using
            Comb.Steps.trans (step?_sound (t := t) (u := t') hstep) (ih t')

/-- Church boolean encodings inside `Comb`. -/
def bTrue : Comb := Comb.K
def bFalse : Comb := Comb.app Comb.K Comb.I

/-- Attempt to decode a Church boolean by applying it to two distinct normal forms. -/
def decodeChurchBoolFuel (fuel : Nat) (b : Comb) : Option Bool :=
  let t := Comb.K
  let f := Comb.S
  let out := reduceFuel fuel (Comb.app (Comb.app b t) f)
  if out = t then
    some true
  else if out = f then
    some false
  else
    none

end SKYExec

end Combinators
end LoF
end HeytingLean
