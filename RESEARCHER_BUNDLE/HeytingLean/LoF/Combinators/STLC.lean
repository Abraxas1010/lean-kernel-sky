/-!
# STLC — minimal simply-typed lambda calculus (Phase 4a baseline)

This module defines a tiny STLC with:
* base type `Bool`,
* function types `A ⟶ B`,
* terms: variables (de Bruijn), application, lambda, boolean literals.

It provides an algorithmic type inference function `infer` and a boolean checker `check`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

namespace STLC

/-! ## Types -/

inductive Ty where
  | bool
  | arrow (a b : Ty)
deriving DecidableEq, Repr

notation:35 a " ⟶ " b => Ty.arrow a b

/-! ## Terms (de Bruijn) -/

inductive Term where
  | var (idx : Nat)
  | app (f a : Term)
  | lam (argTy : Ty) (body : Term)
  | ttrue
  | tfalse
deriving DecidableEq, Repr

abbrev Ctx : Type := List Ty

def ctxGet? : Ctx → Nat → Option Ty
  | [], _ => none
  | t :: _, 0 => some t
  | _ :: ts, Nat.succ i => ctxGet? ts i

/-! ## Algorithmic type inference/checking -/

def infer : Ctx → Term → Option Ty
  | Γ, .var i => ctxGet? Γ i
  | Γ, .app f a =>
      match infer Γ f with
      | some (.arrow tArg tRes) =>
          match infer Γ a with
          | some tA =>
              if tA = tArg then some tRes else none
          | none => none
      | _ => none
  | Γ, .lam tArg body =>
      match infer (tArg :: Γ) body with
      | some tBody => some (tArg ⟶ tBody)
      | none => none
  | _, .ttrue => some .bool
  | _, .tfalse => some .bool

def check (Γ : Ctx) (t : Term) (ty : Ty) : Bool :=
  match infer Γ t with
  | some ty' => decide (ty' = ty)
  | none => false

/-! ## Small sample terms (closed) -/

def tIdBool : Term :=
  .lam .bool (.var 0)

def tConstBool : Term :=
  .lam .bool (.lam .bool (.var 1))

def tAppIdTrue : Term :=
  .app tIdBool .ttrue

def tBadApp : Term :=
  -- (λx:Bool, x) applied to (λy:Bool, y) is ill-typed in STLC.
  .app tIdBool tIdBool

end STLC

end Combinators
end LoF
end HeytingLean
