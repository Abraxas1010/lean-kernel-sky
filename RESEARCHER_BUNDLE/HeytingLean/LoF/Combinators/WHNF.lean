import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.Inductive

/-!
# LeanKernel.WHNF (Phase 9)

Weak-head normalization (WHNF) for the staged kernel expression AST `Expr`
(Phase 8), implemented in a bounded, executable style suitable for later
Scott-encoding / compilation to SKY.

This phase intentionally supports only:
- **ζ-reduction**: unfold `letE` by instantiating its body with the value
- **β-reduction**: reduce `app (lam _ _ _ body) arg` by instantiating `body`

We do *not* yet unfold `const` (needs an environment, later phases), and we do
not perform projection/mdata/etc (not yet present in the staged AST).

Phase 11 adds an *optional* ι-reduction layer via `Inductive.IotaRules`:
use `WHNF.whnfWith rules fuel e` when you want `casesOn`-style iota steps in WHNF.

Phase 13 adds an *optional* δ-reduction layer via a `constValue?` callback:
use `WHNF.whnfWithDelta constValue? rules fuel e` when you want unfolding of constants.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

namespace Expr

variable {Name Param MetaLevel MetaExpr : Type u}

/-- Shift de Bruijn indices: increment every `bvar i` with `i ≥ cutoff` by `inc`. -/
def shiftBVar (cutoff inc : Nat) : Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr
  | .bvar i => if i < cutoff then .bvar i else .bvar (i + inc)
  | .mvar m => .mvar m
  | .sort u => .sort u
  | .const c us => .const c us
  | .app f a => .app (shiftBVar cutoff inc f) (shiftBVar cutoff inc a)
  | .lam bn bi ty body =>
      .lam bn bi (shiftBVar cutoff inc ty) (shiftBVar (cutoff + 1) inc body)
  | .forallE bn bi ty body =>
      .forallE bn bi (shiftBVar cutoff inc ty) (shiftBVar (cutoff + 1) inc body)
  | .letE bn bi ty val body =>
      .letE bn bi (shiftBVar cutoff inc ty) (shiftBVar cutoff inc val) (shiftBVar (cutoff + 1) inc body)
  | .lit l => .lit l

/-- Instantiate de Bruijn indices using a substitution function `σ : Nat → Expr ...`.

This is the standard binder-depth (`k`) formulation:
- `bvar i` with `i < k` is locally bound, unchanged
- `bvar i` with `i ≥ k` is replaced by `shiftBVar 0 k (σ (i-k))`

Binder *types* are not under the binder; binder *bodies* are.
-/
def instantiate (σ : Nat → Expr Name Param MetaLevel MetaExpr) :
    Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr :=
  let rec go (k : Nat) : Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr
    | .bvar i =>
        if i < k then
          .bvar i
        else
          -- `i ≥ k`, so this is a free variable (relative to `k`) to be substituted.
          let j := i - k
          shiftBVar (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) 0 k (σ j)
    | .mvar m => .mvar m
    | .sort u => .sort u
    | .const c us => .const c us
    | .app f a => .app (go k f) (go k a)
    | .lam bn bi ty body => .lam bn bi (go k ty) (go (k + 1) body)
    | .forallE bn bi ty body => .forallE bn bi (go k ty) (go (k + 1) body)
    | .letE bn bi ty val body => .letE bn bi (go k ty) (go k val) (go (k + 1) body)
    | .lit l => .lit l
  fun e => go 0 e

/-- Instantiate the *outermost* bound variable (index 0) with value `v`. -/
def instantiate1 (v : Expr Name Param MetaLevel MetaExpr) (body : Expr Name Param MetaLevel MetaExpr) :
    Expr Name Param MetaLevel MetaExpr :=
  instantiate
    (fun
      | 0 => v
      | n + 1 => .bvar n)
    body

@[simp] theorem shiftBVar_bvar_lt (cutoff inc i : Nat) (h : i < cutoff) :
    shiftBVar (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) cutoff inc (.bvar i) = .bvar i := by
  simp [shiftBVar, h]

@[simp] theorem shiftBVar_bvar_ge (cutoff inc i : Nat) (h : ¬ i < cutoff) :
    shiftBVar (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) cutoff inc (.bvar i) = .bvar (i + inc) := by
  simp [shiftBVar, h]

end Expr

namespace WHNF

variable {Name Param MetaLevel MetaExpr : Type u}

/-- One weak-head reduction step (β/ζ/δ/ι), parameterized by:
- `constValue?` for δ-reduction (unfolding constants),
- `casesOn`-style iota rules (Phase 11).

When `constValue?` returns `none`, δ-reduction is disabled. -/
def whnfStepWithDelta?
    (constValue? : Name → List (ULevel Param MetaLevel) → Option (Expr Name Param MetaLevel MetaExpr))
    (rules : Inductive.IotaRules Name) :
    Expr Name Param MetaLevel MetaExpr → Option (Expr Name Param MetaLevel MetaExpr)
  | .letE _ _ _ val body =>
      some (Expr.instantiate1 (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) val body)
  | .const c us =>
      constValue? c us
  | e@(.app f a) =>
      match Inductive.iotaStep? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) rules e with
      | some e' => some e'
      | none =>
          match whnfStepWithDelta? constValue? rules f with
          | some f' => some (.app f' a)
          | none =>
              match f with
              | .lam _ _ _ body =>
                  some (Expr.instantiate1 (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) a body)
              | _ => none
  | _ => none

/-- One weak-head reduction step (β/ζ/ι), parameterized by `casesOn`-style iota rules. -/
def whnfStepWith? (rules : Inductive.IotaRules Name) :
    Expr Name Param MetaLevel MetaExpr → Option (Expr Name Param MetaLevel MetaExpr) :=
  whnfStepWithDelta? (fun _ _ => none) rules

/-- One weak-head reduction step (β/ζ), with a left-spine strategy for `app`. -/
def whnfStep? :
    Expr Name Param MetaLevel MetaExpr → Option (Expr Name Param MetaLevel MetaExpr)
  | .letE _ _ _ val body =>
      some (Expr.instantiate1 (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) val body)
  | .app f a =>
      match whnfStep? f with
      | some f' => some (.app f' a)
      | none =>
          match f with
          | .lam _ _ _ body =>
              some (Expr.instantiate1 (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) a body)
              | _ => none
  | _ => none

/-- Bounded WHNF with δ/ι rules: iterates `whnfStepWithDelta?` up to `fuel` times. -/
def whnfWithDelta
    (constValue? : Name → List (ULevel Param MetaLevel) → Option (Expr Name Param MetaLevel MetaExpr))
    (rules : Inductive.IotaRules Name) :
    Nat → Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr
  | 0, e => e
  | fuel + 1, e =>
      match whnfStepWithDelta? constValue? rules e with
      | some e' => whnfWithDelta constValue? rules fuel e'
      | none => e

/-- Bounded WHNF with iota rules: iterates `whnfStepWith?` up to `fuel` times. -/
def whnfWith (rules : Inductive.IotaRules Name) :
    Nat → Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr
  :=
  whnfWithDelta (fun _ _ => none) rules

/-- Bounded WHNF: iterates `whnfStep?` up to `fuel` times. -/
def whnf :
    Nat → Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr
  | 0, e => e
  | fuel + 1, e =>
      match whnfStep? e with
      | some e' => whnf fuel e'
      | none => e

end WHNF

end LeanKernel
end LoF
end HeytingLean
