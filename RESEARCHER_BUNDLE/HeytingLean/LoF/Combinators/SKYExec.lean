import HeytingLean.LoF.Combinators.SKY

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

/-- Deterministic one-step SKY reduction (leftmost-outermost). -/
def step? : Comb → Option Comb
  | Comb.app (Comb.app Comb.K x) _ => some x
  | Comb.app (Comb.app (Comb.app Comb.S x) y) z =>
      some (Comb.app (Comb.app x z) (Comb.app y z))
  | Comb.app Comb.Y f =>
      some (Comb.app f (Comb.app Comb.Y f))
  | Comb.app f a =>
      match step? f with
      | some f' => some (Comb.app f' a)
      | none =>
          match step? a with
          | some a' => some (Comb.app f a')
          | none => none
  | _ => none

/-- Reduce for at most `fuel` steps, stopping early at normal forms. -/
def reduceFuel : Nat → Comb → Comb
  | 0, t => t
  | Nat.succ n, t =>
      match step? t with
      | some t' => reduceFuel n t'
      | none => t

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

