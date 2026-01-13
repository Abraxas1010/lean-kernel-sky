import HeytingLean.LoF.LeanKernel.DefEq

/-!
# LeanKernel.Infer (Phase 12)

Fuel-bounded, executable type inference/checking for the staged kernel AST `Expr`.

This is a deliberately small “core kernel” algorithm for a dependent Π/λ calculus with:
- `Sort` (`Expr.sort`) universes,
- `forallE` (Π-types),
- `lam` (λ-abstraction),
- `app` (application),
- `letE` (ζ via substitution in the inferred type),
- `bvar` (de Bruijn bound variables),
- `const`/`mvar`/`lit` via a parameterized lookup interface.

It is **not** a full Lean elaborator:
- no implicit argument synthesis,
- no coercions,
- no general δ-reduction unless provided via `Config.constValue?` (Phase 13 environment),
- no metavariable assignment/unification.

The intent is to provide a staged, verifiable executable core that later phases can
compile to SKY and relate to Lean4Lean.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF.LeanKernel

namespace Infer

open Expr

variable {Name Param MetaLevel MetaExpr : Type u}

/-- De Bruijn typing context: `tys[i]` is the type of `bvar i` *in the context
where it was introduced*. When we retrieve it from a larger context, we lift it. -/
structure Ctx (Name Param MetaLevel MetaExpr : Type u) where
  tys : List (Expr Name Param MetaLevel MetaExpr)

namespace Ctx

def empty : Ctx Name Param MetaLevel MetaExpr := { tys := [] }

def extend (ctx : Ctx Name Param MetaLevel MetaExpr) (ty : Expr Name Param MetaLevel MetaExpr) :
    Ctx Name Param MetaLevel MetaExpr :=
  { tys := ty :: ctx.tys }

/-- Lookup the type of `bvar i` and lift it into the current context. -/
def bvarType? (ctx : Ctx Name Param MetaLevel MetaExpr) (i : Nat) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  match ctx.tys[i]? with
  | none => none
  | some ty =>
      -- `ty` was recorded in a context that is `i+1` binders smaller.
      some (Expr.shiftBVar (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) 0 (i + 1) ty)

end Ctx

/-- External information required by the algorithmic kernel checker. -/
structure Config (Name Param MetaLevel MetaExpr : Type u) where
  /-- Optional ι-reduction rules used by WHNF/DefEq during inference. -/
  iotaRules : Inductive.IotaRules Name := Inductive.IotaRules.empty (Name := Name)
  /-- Type of a constant (already instantiated at the provided universe levels, if desired). -/
  constType? :
      Name → List (ULevel Param MetaLevel) → Option (Expr Name Param MetaLevel MetaExpr) :=
    fun _ _ => none
  /-- Optional definitional unfolding for constants (δ-reduction), already instantiated at universe levels. -/
  constValue? :
      Name → List (ULevel Param MetaLevel) → Option (Expr Name Param MetaLevel MetaExpr) :=
    fun _ _ => none
  /-- Type of an expression metavariable. -/
  mvarType? : MetaExpr → Option (Expr Name Param MetaLevel MetaExpr) := fun _ => none
  /-- Type of a literal. -/
  litType? : Literal → Option (Expr Name Param MetaLevel MetaExpr) := fun _ => none

namespace Config

def empty : Config Name Param MetaLevel MetaExpr := {}

end Config

variable [DecidableEq Name] [DecidableEq Param] [DecidableEq MetaLevel] [DecidableEq MetaExpr]

mutual

/-- Fuel-bounded algorithmic inference (Phase 12).

Returns `none` on failure or when fuel is exhausted.
-/
def infer? (cfg : Config Name Param MetaLevel MetaExpr) :
    Nat →
    Ctx Name Param MetaLevel MetaExpr →
    Expr Name Param MetaLevel MetaExpr →
    Option (Expr Name Param MetaLevel MetaExpr)
  | 0, _, _ => none
  | fuel + 1, ctx, e =>
      match e with
      | .bvar i => ctx.bvarType? i
      | .mvar m => cfg.mvarType? m
      | .lit l => cfg.litType? l
      | .sort u => some (.sort (.succ u))
      | .const c us => cfg.constType? c us
      | .app f a =>
          match infer? cfg fuel ctx f with
          | none => none
          | some tf =>
              let tfWhnf :=
                WHNF.whnfWithDelta (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
                  cfg.constValue? cfg.iotaRules (fuel + 1) tf
              match tfWhnf with
              | .forallE _ _ dom body =>
                  match infer? cfg fuel ctx a with
                  | none => none
                  | some ta =>
                      if DefEq.isDefEqWithDelta (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
                          cfg.constValue? cfg.iotaRules (fuel + 1) ta dom then
                        some (Expr.instantiate1 (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) a body)
                      else
                        none
              | _ => none
      | .lam bn bi ty body =>
          match inferSort? cfg fuel ctx ty with
          | none => none
          | some _ =>
              match infer? cfg fuel (ctx.extend ty) body with
              | none => none
              | some bodyTy =>
                  some (.forallE bn bi ty bodyTy)
      | .forallE _ _ ty body =>
          match inferSort? cfg fuel ctx ty with
          | none => none
          | some u =>
              match inferSort? cfg fuel (ctx.extend ty) body with
              | none => none
              | some v =>
                  some (.sort (.imax u v))
      | .letE _ _ ty val body =>
          match inferSort? cfg fuel ctx ty with
          | none => none
          | some _ =>
              match infer? cfg fuel ctx val with
              | none => none
              | some tVal =>
                  if DefEq.isDefEqWithDelta (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
                      cfg.constValue? cfg.iotaRules (fuel + 1) tVal ty then
                    match infer? cfg fuel
                        (ctx.extend ty) body with
                    | none => none
                    | some bodyTy =>
                        some (Expr.instantiate1 (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) val bodyTy)
                  else
                    none

/-- Infer the universe level `u` such that `e : Sort u`. -/
def inferSort? (cfg : Config Name Param MetaLevel MetaExpr) :
    Nat →
    Ctx Name Param MetaLevel MetaExpr →
    Expr Name Param MetaLevel MetaExpr →
    Option (ULevel Param MetaLevel)
  | 0, _, _ => none
  | fuel + 1, ctx, e =>
      match infer? cfg fuel ctx e with
      | some (.sort u) => some u
      | _ => none

end

/-- Boolean checking wrapper: `true` iff we can infer a type for `e` and it is defeq to `ty`. -/
def check (cfg : Config Name Param MetaLevel MetaExpr) (fuel : Nat) (ctx : Ctx Name Param MetaLevel MetaExpr)
    (e ty : Expr Name Param MetaLevel MetaExpr) : Bool :=
  match infer? cfg fuel ctx e with
  | none => false
  | some ty' =>
      DefEq.isDefEqWithDelta (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
        cfg.constValue? cfg.iotaRules fuel ty' ty

end Infer

end LeanKernel
end LoF
end HeytingLean
