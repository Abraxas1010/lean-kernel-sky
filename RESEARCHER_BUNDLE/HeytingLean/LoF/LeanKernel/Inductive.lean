import HeytingLean.LoF.LeanKernel.Expression

/-!
# LeanKernel.Inductive (Phase 11)

Executable scaffolding for inductive reduction.

This phase introduces a small, *data-driven* interface for **ι-reduction**
specialized to `casesOn`-style recursors:

`casesOn params minors major`

When `major` is a constructor application, we reduce to the corresponding minor
applied to the constructor fields.

This is intentionally minimal and environment-free. Later phases will connect
these rules to a real kernel environment (constants, inductive declarations,
recursors, and δ-reduction).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

namespace Inductive

open Expr

variable {Name Param MetaLevel MetaExpr : Type u}

/-! ## Application spine utilities -/

private def getAppFnArgs.go :
    Expr Name Param MetaLevel MetaExpr →
    List (Expr Name Param MetaLevel MetaExpr) →
    Expr Name Param MetaLevel MetaExpr × List (Expr Name Param MetaLevel MetaExpr)
  | .app f a, argsRev => getAppFnArgs.go f (a :: argsRev)
  | e, argsRev => (e, argsRev)

/-- Decompose an expression into its head function and its (left-spine) arguments. -/
def getAppFnArgs (e : Expr Name Param MetaLevel MetaExpr) :
    Expr Name Param MetaLevel MetaExpr × List (Expr Name Param MetaLevel MetaExpr) :=
  getAppFnArgs.go e []

/-- Build an application from a head and a list of arguments. -/
def mkAppN (f : Expr Name Param MetaLevel MetaExpr) (args : List (Expr Name Param MetaLevel MetaExpr)) :
    Expr Name Param MetaLevel MetaExpr :=
  args.foldl (fun acc a => Expr.app acc a) f

/-! ## `casesOn`-style ι-reduction -/

structure CtorSpec (Name : Type u) where
  name : Name
  numFields : Nat
deriving Repr

/-- A minimal spec for `casesOn`-style recursors.

Argument order is assumed to be:
`recursor params... minor₀ ... minorₖ major`.

`numParams` counts the prefix arguments before the minors.
Minors are ordered to match `ctors`.
-/
structure CasesOnSpec (Name : Type u) where
  recursor : Name
  numParams : Nat
  ctors : List (CtorSpec Name)
deriving Repr

structure IotaRules (Name : Type u) where
  beqName : Name → Name → Bool
  casesOnSpecs : List (CasesOnSpec Name)

namespace IotaRules

def empty : IotaRules Name := { beqName := fun _ _ => false, casesOnSpecs := [] }

end IotaRules

private def ctorIndex? (beqName : Name → Name → Bool) (ctors : List (CtorSpec Name)) (c : Name) : Option Nat :=
  let rec go : List (CtorSpec Name) → Nat → Option Nat
    | [], _ => none
    | d :: ds, i =>
        if beqName d.name c then
          some i
        else
          go ds (i + 1)
  go ctors 0

private def ctorArity? (ctors : List (CtorSpec Name)) (idx : Nat) : Option Nat :=
  match ctors[idx]? with
  | some c => some c.numFields
  | none => none

private def casesOnStep?
    (beqName : Name → Name → Bool)
    (spec : CasesOnSpec Name)
    (e : Expr Name Param MetaLevel MetaExpr) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  let (fn, args) := getAppFnArgs (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) e
  match fn with
  | .const c _ =>
      if beqName c spec.recursor then
        let expected := spec.numParams + spec.ctors.length + 1
        if args.length = expected then
          match args.getLast? with
          | none => none
          | some major =>
              let (majorFn, majorArgs) :=
                getAppFnArgs (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) major
              match majorFn with
              | .const ctorName _ =>
                  match ctorIndex? (beqName := beqName) (ctors := spec.ctors) ctorName with
                  | none => none
                  | some idx =>
                      match ctorArity? (ctors := spec.ctors) idx with
                      | none => none
                      | some arity =>
                          if majorArgs.length = arity then
                            match args[spec.numParams + idx]? with
                            | none => none
                            | some minor =>
                                some (mkAppN (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) minor majorArgs)
                          else
                            none
              | _ => none
        else
          none
      else
        none
  | _ => none

/-- One ι-reduction step using the provided rules, if the expression is a `casesOn` redex. -/
def iotaStep?
    (rules : IotaRules Name)
    (e : Expr Name Param MetaLevel MetaExpr) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  let rec go : List (CasesOnSpec Name) → Option (Expr Name Param MetaLevel MetaExpr)
    | [] => none
    | s :: ss =>
        match casesOnStep? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) rules.beqName s e with
        | some e' => some e'
        | none => go ss
  go rules.casesOnSpecs

/-! ## Example rules for `Name := String` (used by sanity tests) -/

namespace Examples

def boolCasesOn : CasesOnSpec String :=
  { recursor := "Bool.casesOn"
    numParams := 1
    ctors :=
      [ { name := "Bool.true", numFields := 0 }
      , { name := "Bool.false", numFields := 0 } ] }

def natCasesOn : CasesOnSpec String :=
  { recursor := "Nat.casesOn"
    numParams := 1
    ctors :=
      [ { name := "Nat.zero", numFields := 0 }
      , { name := "Nat.succ", numFields := 1 } ] }

def rules : IotaRules String :=
  { beqName := fun a b => decide (a = b)
    casesOnSpecs := [boolCasesOn, natCasesOn] }

end Examples

end Inductive

end LeanKernel
end LoF
end HeytingLean
