import HeytingLean.LoF.LeanKernel.WHNF

/-!
# LeanKernel.DefEq (Phase 10)

Fuel-bounded definitional equality for the staged kernel expression AST `Expr`.

This phase is intentionally **minimal** and **executable**:
- uses Phase 9 WHNF (β/ζ only) as the head-reduction engine,
- compares WHNF results by structural congruence on the 9 constructors,
- compares `sort`/universe levels by closed evaluation when possible.

Later phases will extend this with:
- δ-reduction (constants + environment) via `DefEq.isDefEqWithDelta`,
- ι-reduction (inductives) via `Inductive.IotaRules`,
- η (if needed),
- metavariable assignment / constraint solving.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

namespace ULevel

variable {Param Meta : Type u}

/-- `true` iff the level contains no parameters or metavariables. -/
def isClosed : ULevel Param Meta → Bool
  | .zero => true
  | .succ u => isClosed u
  | .max a b => isClosed a && isClosed b
  | .imax a b => isClosed a && isClosed b
  | .param _ => false
  | .mvar _ => false

/-- Evaluate a level to a natural number iff it is closed. -/
def evalClosed? (u : ULevel Param Meta) : Option Nat :=
  if isClosed u then
    some (ULevel.eval (Param := Param) (Meta := Meta) (fun _ => 0) (fun _ => 0) u)
  else
    none

end ULevel

namespace DefEq

open HeytingLean.LoF.LeanKernel.WHNF

variable {Name Param MetaLevel MetaExpr : Type u}
variable [DecidableEq Name] [DecidableEq Param] [DecidableEq MetaLevel] [DecidableEq MetaExpr]

private def ulevelDefEq (u v : ULevel Param MetaLevel) : Bool :=
  match ULevel.evalClosed? (Param := Param) (Meta := MetaLevel) u,
        ULevel.evalClosed? (Param := Param) (Meta := MetaLevel) v with
  | some nu, some nv => decide (nu = nv)
  | _, _ => decide (u = v)

private def ulevelListDefEq : List (ULevel Param MetaLevel) → List (ULevel Param MetaLevel) → Bool
  | [], [] => true
  | u :: us, v :: vs => ulevelDefEq u v && ulevelListDefEq us vs
  | _, _ => false

/-- Fuel-bounded definitional equality (Phase 10).

Behavior:
- each recursive call consumes 1 unit of fuel,
- at each call, both sides are normalized to WHNF using the available fuel,
- mismatched WHNF shapes are treated as `false` (no η, no unification/constraints).
-/
def isDefEqWithDelta
    (constValue? : Name → List (ULevel Param MetaLevel) → Option (Expr Name Param MetaLevel MetaExpr))
    (rules : Inductive.IotaRules Name) :
    Nat →
    Expr Name Param MetaLevel MetaExpr →
    Expr Name Param MetaLevel MetaExpr →
    Bool
  | 0, e₁, e₂ => decide (e₁ = e₂)
  | fuel + 1, e₁, e₂ =>
      let e₁' :=
        WHNF.whnfWithDelta (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) constValue? rules (fuel + 1) e₁
      let e₂' :=
        WHNF.whnfWithDelta (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) constValue? rules (fuel + 1) e₂
      match e₁', e₂' with
      | .bvar i, .bvar j => decide (i = j)
      | .mvar m, .mvar n => decide (m = n)
      | .sort u, .sort v => ulevelDefEq u v
      | .const c us, .const d vs => decide (c = d) && ulevelListDefEq us vs
      | .app f a, .app g b => isDefEqWithDelta constValue? rules fuel f g && isDefEqWithDelta constValue? rules fuel a b
      -- binder name / binderInfo are ignored for conversion.
      | .lam _ _ ty body, .lam _ _ ty' body' => isDefEqWithDelta constValue? rules fuel ty ty' && isDefEqWithDelta constValue? rules fuel body body'
      | .forallE _ _ ty body, .forallE _ _ ty' body' => isDefEqWithDelta constValue? rules fuel ty ty' && isDefEqWithDelta constValue? rules fuel body body'
      | .lit l, .lit r => decide (l = r)
      | _, _ => false

/-- Fuel-bounded definitional equality (Phase 10), with optional ι-reduction rules. -/
def isDefEqWith (rules : Inductive.IotaRules Name) :
    Nat →
    Expr Name Param MetaLevel MetaExpr →
    Expr Name Param MetaLevel MetaExpr →
    Bool :=
  isDefEqWithDelta (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) (fun _ _ => none) rules

/-- Fuel-bounded definitional equality (Phase 10), with no ι-reduction rules. -/
def isDefEq :
    Nat →
    Expr Name Param MetaLevel MetaExpr →
    Expr Name Param MetaLevel MetaExpr →
    Bool :=
  isDefEqWith (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) (Inductive.IotaRules.empty (Name := Name))

end DefEq

end LeanKernel
end LoF
end HeytingLean
