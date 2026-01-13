import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.Inductive
import HeytingLean.LoF.LeanKernel.Infer

/-!
# LeanKernel.Environment (Phase 13)

An executable, *data-driven* kernel environment layer for the staged expression AST `Expr`.

This phase provides:
- A minimal constant/declaration table (types + optional definitional bodies).
- A place to store `casesOn`-style ι-reduction specs (Phase 11), producing `Inductive.IotaRules`.
- Conversion to Phase 12's `Infer.Config` (so the typechecker can be run against an environment).

The goal is to keep the representation lightweight (list-based, no meta-logic),
while providing the hooks needed for δ-reduction (unfolding constants) in later phases.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

namespace Environment

open Expr

variable {Name Param MetaLevel MetaExpr : Type u}

/-- A constant declaration: universe-instantiated type, and an optional universe-instantiated value. -/
structure ConstDecl (Name Param MetaLevel MetaExpr : Type u) where
  name : Name
  type : List (ULevel Param MetaLevel) → Expr Name Param MetaLevel MetaExpr
  value? : Option (List (ULevel Param MetaLevel) → Expr Name Param MetaLevel MetaExpr) := none

namespace ConstDecl

variable {Name Param MetaLevel MetaExpr : Type u}

def ofType (name : Name) (ty : Expr Name Param MetaLevel MetaExpr) : ConstDecl Name Param MetaLevel MetaExpr :=
  { name := name, type := fun _ => ty, value? := none }

def ofDef (name : Name) (ty val : Expr Name Param MetaLevel MetaExpr) : ConstDecl Name Param MetaLevel MetaExpr :=
  { name := name, type := fun _ => ty, value? := some (fun _ => val) }

end ConstDecl

/-- A minimal kernel environment.

We keep everything parameterized by:
- a name equality predicate `beqName` (so `Name` need not be `DecidableEq`),
- a list of constant declarations,
- optional `casesOn` specs for ι-reduction (Phase 11).

This is deliberately *not* a full Lean environment (no modules, no reducibility hints, etc.). -/
structure Env (Name Param MetaLevel MetaExpr : Type u) where
  beqName : Name → Name → Bool
  consts : List (ConstDecl Name Param MetaLevel MetaExpr) := []
  casesOnSpecs : List (Inductive.CasesOnSpec Name) := []
  mvarType? : MetaExpr → Option (Expr Name Param MetaLevel MetaExpr) := fun _ => none
  litType? : Literal → Option (Expr Name Param MetaLevel MetaExpr) := fun _ => none

namespace Env

variable {Name Param MetaLevel MetaExpr : Type u}

def iotaRules (env : Env Name Param MetaLevel MetaExpr) : Inductive.IotaRules Name :=
  { beqName := env.beqName, casesOnSpecs := env.casesOnSpecs }

def addConst (env : Env Name Param MetaLevel MetaExpr) (d : ConstDecl Name Param MetaLevel MetaExpr) :
    Env Name Param MetaLevel MetaExpr :=
  { env with consts := d :: env.consts }

def addCasesOnSpec (env : Env Name Param MetaLevel MetaExpr) (s : Inductive.CasesOnSpec Name) :
    Env Name Param MetaLevel MetaExpr :=
  { env with casesOnSpecs := s :: env.casesOnSpecs }

def constDecl? (env : Env Name Param MetaLevel MetaExpr) (c : Name) : Option (ConstDecl Name Param MetaLevel MetaExpr) :=
  env.consts.find? (fun d => env.beqName d.name c)

def constType? (env : Env Name Param MetaLevel MetaExpr) (c : Name) (us : List (ULevel Param MetaLevel)) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  (constDecl? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) env c).map (fun d => d.type us)

def constValue? (env : Env Name Param MetaLevel MetaExpr) (c : Name) (us : List (ULevel Param MetaLevel)) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  match constDecl? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) env c with
  | none => none
  | some d => d.value?.map (fun f => f us)

def toInferConfig (env : Env Name Param MetaLevel MetaExpr) : Infer.Config Name Param MetaLevel MetaExpr :=
  { iotaRules := iotaRules (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) env
    constType? := fun c us => constType? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) env c us
    constValue? := fun c us => constValue? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) env c us
    mvarType? := env.mvarType?
    litType? := env.litType? }

end Env

end Environment

end LeanKernel
end LoF
end HeytingLean

