import HeytingLean.LoF.LeanKernel.UniverseLevel
import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.Inductive
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.WHNFSKY
import HeytingLean.LoF.LeanKernel.WHNFDeltaSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.InferSKY
import HeytingLean.LoF.LeanKernel.KernelSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

/-!
# LeanKernelSanity

Compile-time sanity checks for the staged “Lean from LoF” kernel pipeline.

Phase 7 check: universe levels (`ULevel`) exist with an `eval` semantics and a Scott encoding hook.
-/

namespace HeytingLean.Tests.LeanKernelSanity

open HeytingLean.LoF
open HeytingLean.LoF.LeanKernel

namespace Phase7

abbrev U : Type := ULevel Unit Unit

def ρ0 : Unit → Nat := fun _ => 0

example : U := .zero
example : U := .succ .zero
example : U := .max (.succ .zero) .zero
example : U := .imax (.succ .zero) .zero

example : ULevel.eval (Param := Unit) (Meta := Unit) ρ0 ρ0 (.zero) = 0 := by rfl
example : ULevel.eval (Param := Unit) (Meta := Unit) ρ0 ρ0 (.succ .zero) = 1 := by rfl
example : ULevel.eval (Param := Unit) (Meta := Unit) ρ0 ρ0 (.imax (.succ .zero) .zero) = 0 := by
  simp [ULevel.eval]

-- Scott encoding hook exists (later phases will use this to compile levels to SKY).
#check ULevel.Scott.encode
#check ULevel.Scott.compileClosed?

end Phase7

namespace Phase8

open HeytingLean.LoF.LeanKernel

abbrev E : Type := Expr Unit Unit Unit Unit

def encUnit : Unit → Expr.Scott.L := fun _ => HeytingLean.LoF.Combinators.Bracket.Lam.K
def encString : String → Expr.Scott.L := fun _ => HeytingLean.LoF.Combinators.Bracket.Lam.K

example : E := .bvar 0
example : E := .sort (.succ .zero)
example : E := .app (.bvar 0) (.lit (.natVal 7))
example : E := .lam () .default (.sort .zero) (.bvar 0)

#check Expr.Scott.encode
#check Expr.Scott.compileClosed?

end Phase8

namespace Phase9

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.WHNF

abbrev E : Type := Expr Unit Unit Unit Unit

def idLam : E := .lam () .default (.sort .zero) (.bvar 0)
def arg : E := .lit (.natVal 3)

-- β-reduction at the head.
example : WHNF.whnf (Name := Unit) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 1 (.app idLam arg) = arg := by
  rfl

-- ζ-reduction for let-expressions.
def letId : E := .letE () .default (.sort .zero) arg (.bvar 0)

example : WHNF.whnf (Name := Unit) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 1 letId = arg := by
  rfl

-- Left spine: reduce the function part of an application before attempting β.
def letLam : E := .letE () .default (.sort .zero) idLam (.bvar 0)

example :
    WHNF.whnf (Name := Unit) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 2 (.app letLam arg) =
      arg := by
  rfl

end Phase9

namespace Phase16

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.WHNFSKY

-- Compile-time presence checks: computation-plane λ-encodings exist.
#check WHNFSKY.whnfStepSky
#check WHNFSKY.whnfSky
#check WHNFSKY.whnfComb?
#check WHNFSKY.runWhnfTagFuel

end Phase16

namespace Phase17

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.DefEqSKY

-- Compile-time presence checks: computation-plane `isDefEq` encoding exists.
#check DefEqSKY.isDefEqSky
#check DefEqSKY.isDefEqSkyWith
#check DefEqSKY.isDefEqComb?
#check DefEqSKY.runIsDefEqFuel

end Phase17

namespace Phase18

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.InferSKY

-- Compile-time presence checks: computation-plane inference exists.
#check InferSKY.inferSky
#check InferSKY.inferSkyWith
#check InferSKY.inferComb?
#check InferSKY.runInferTagFuel
#check InferSKY.checkSky
#check InferSKY.checkSkyWith
#check InferSKY.checkComb?
#check InferSKY.runCheckFuel

end Phase18

namespace Phase19

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.KernelSKY

-- Compile-time presence checks: Phase 19 integration bundle exists.
#check KernelSKY.Compiled
#check KernelSKY.compile?
#check KernelSKY.runWhnfTagFuelWith
#check KernelSKY.runIsDefEqFuelWith
#check KernelSKY.runInferTagFuelWith
#check KernelSKY.runCheckFuelWith

end Phase19

namespace Phase24

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.FullKernelSKY

-- Compile-time presence checks: β/ζ/δ/ι bundle exists.
#check FullKernelSKY.whnfFullSky
#check FullKernelSKY.isDefEqFullSky
#check FullKernelSKY.inferFullSky
#check FullKernelSKY.checkFullSky
#check FullKernelSKY.compileFull?

end Phase24

namespace Phase21

open HeytingLean.LoF.LeanKernel.EnvironmentSKY

-- Compile-time presence checks: environment encoding + lookup exist.
#check EnvironmentSKY.constDeclEncode
#check EnvironmentSKY.envLookup?
#check EnvironmentSKY.constType?
#check EnvironmentSKY.constValue?
#check EnvironmentSKY.envEncode
#check EnvironmentSKY.envComb?
#check EnvironmentSKY.runConstTypeTagFuel
#check EnvironmentSKY.runConstValueTagFuel

end Phase21

namespace Phase22

open HeytingLean.LoF.LeanKernel.WHNFDeltaSKY

-- Compile-time presence checks: δ-aware WHNF encoding exists.
#check WHNFDeltaSKY.whnfStepDeltaSky
#check WHNFDeltaSKY.whnfDeltaSky
#check WHNFDeltaSKY.whnfDeltaComb?
#check WHNFDeltaSKY.runWhnfDeltaTagFuel

end Phase22

namespace Phase23

open HeytingLean.LoF.LeanKernel.WHNFIotaSKY

-- Compile-time presence checks: ι-aware WHNF encoding exists.
#check WHNFIotaSKY.iotaStepSky
#check WHNFIotaSKY.whnfStepIotaSky
#check WHNFIotaSKY.whnfIotaSky
#check WHNFIotaSKY.whnfIotaComb?
#check WHNFIotaSKY.runWhnfIotaTagFuel

end Phase23

namespace Phase10

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.WHNF
open HeytingLean.LoF.LeanKernel.DefEq

abbrev E : Type := Expr Unit Unit Unit Unit

def idLam : E := .lam () .default (.sort .zero) (.bvar 0)
def arg : E := .lit (.natVal 3)

-- With fuel, definitional equality sees β-reduction.
example :
    DefEq.isDefEq (Name := Unit) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 5 (.app idLam arg) arg =
      true := by
  rfl

-- With no fuel, we fall back to syntactic equality.
example :
    DefEq.isDefEq (Name := Unit) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 0 (.app idLam arg) arg =
      false := by
  rfl

-- Closed universe level comparison uses numeric evaluation.
def u1 : ULevel Unit Unit := .max (.succ .zero) .zero
def u2 : ULevel Unit Unit := .succ .zero

example :
    DefEq.isDefEq (Name := Unit) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 3 (.sort u1) (.sort u2) =
      true := by
  rfl

-- Binder names / binderInfo are ignored by conversion.
abbrev E' : Type := Expr Nat Unit Unit Unit

def lamA : E' := .lam 0 .implicit (.sort .zero) (.bvar 0)
def lamB : E' := .lam 1 .default (.sort .zero) (.bvar 0)

example : DefEq.isDefEq (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 2 lamA lamB = true := by
  rfl

-- Const levels compare by closed level equality when possible.
def c1 : E' := .const 7 [u1]
def c2 : E' := .const 7 [u2]

example : DefEq.isDefEq (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 2 c1 c2 = true := by
  rfl

example :
    DefEq.isDefEq (Name := Unit) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) 2 (.lit (.natVal 0)) (.lit (.natVal 1)) =
      false := by
  rfl

end Phase10

namespace Phase11

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.WHNF
open HeytingLean.LoF.LeanKernel.DefEq
open HeytingLean.LoF.LeanKernel.Inductive

abbrev E : Type := Expr Nat Unit Unit Unit

def nBoolCasesOn : Nat := 0
def nBoolTrue : Nat := 1
def nBoolFalse : Nat := 2
def nNatCasesOn : Nat := 3
def nNatZero : Nat := 4
def nNatSucc : Nat := 5

def rules : Inductive.IotaRules Nat :=
  { beqName := Nat.beq
    casesOnSpecs :=
      [ { recursor := nBoolCasesOn
          numParams := 1
          ctors :=
            [ { name := nBoolTrue, numFields := 0 }
            , { name := nBoolFalse, numFields := 0 } ] }
      , { recursor := nNatCasesOn
          numParams := 1
          ctors :=
            [ { name := nNatZero, numFields := 0 }
            , { name := nNatSucc, numFields := 1 } ] } ] }

def appN (f : E) (args : List E) : E :=
  Inductive.mkAppN (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) f args

/-! ### Bool.casesOn iota -/

def boolTrue : E := .const nBoolTrue []
def boolFalse : E := .const nBoolFalse []
def boolMotive : E := .sort .zero
def boolThen : E := .lit (.natVal 10)
def boolElse : E := .lit (.natVal 20)

def boolCasesOn (b : E) : E :=
  appN (.const nBoolCasesOn []) [boolMotive, boolThen, boolElse, b]

example :
    WHNF.whnfWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules 1 (boolCasesOn boolTrue) =
      boolThen := by
  native_decide

example :
    WHNF.whnfWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules 1 (boolCasesOn boolFalse) =
      boolElse := by
  native_decide

example :
    DefEq.isDefEqWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules 3 (boolCasesOn boolTrue) boolThen =
      true := by
  native_decide

/-! ### Nat.casesOn iota -/

def natZero : E := .const nNatZero []
def natSucc (n : E) : E := .app (.const nNatSucc []) n

def natMotive : E := .sort .zero
def natZeroCase : E := .lit (.natVal 0)
def natSuccCase : E := .lam 0 .default (.sort .zero) (.bvar 0)
def natArg : E := .lit (.natVal 7)

def natCasesOn (n : E) : E :=
  appN (.const nNatCasesOn []) [natMotive, natZeroCase, natSuccCase, n]

-- One step of WHNF performs the iota step, exposing an application of the succ-branch.
example :
    WHNF.whnfWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules 1 (natCasesOn (natSucc natArg)) =
      .app natSuccCase natArg := by
  native_decide

-- With one more step of fuel, we also see the β-step of the succ-branch lambda.
example :
    WHNF.whnfWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules 2 (natCasesOn (natSucc natArg)) =
      natArg := by
  native_decide

example :
    WHNF.whnfWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules 2 (natCasesOn natZero) =
      natZeroCase := by
  native_decide

end Phase11

namespace Phase12

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.Infer

abbrev E : Type := Expr Nat Unit Unit Unit

def cNat : Nat := 100
def cBool : Nat := 101
def cTrue : Nat := 102
def cZero : Nat := 103

def tyNat : E := .const cNat []
def tyBool : E := .const cBool []

def cfg : Infer.Config Nat Unit Unit Unit :=
  { constType? :=
      fun c _us =>
        if c = cNat then
          some (.sort (.succ .zero))
        else if c = cBool then
          some (.sort (.succ .zero))
        else if c = cTrue then
          some tyBool
        else if c = cZero then
          some tyNat
        else
          none
    litType? :=
      fun
        | .natVal _ => some tyNat
        | .strVal _ => none }

def Γ0 : Infer.Ctx Nat Unit Unit Unit := Infer.Ctx.empty

def idNat : E := .lam 0 .default tyNat (.bvar 0)
def argNat : E := .lit (.natVal 3)
def argBool : E := .const cTrue []

example : Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg 10 Γ0 argNat = some tyNat := by
  native_decide

example :
    Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg 10 Γ0 idNat =
      some (.forallE 0 .default tyNat tyNat) := by
  native_decide

example :
    Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg 20 Γ0 (.app idNat argNat) =
      some tyNat := by
  native_decide

-- Ill-typed: applying a Nat function to a Bool.
example :
    Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg 20 Γ0 (.app idNat argBool) =
      none := by
  native_decide

-- ζ: let x := 3 in x, inferred type is Nat.
def letId : E := .letE 0 .default tyNat argNat (.bvar 0)

example :
    Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg 20 Γ0 letId =
      some tyNat := by
  native_decide

-- `Nat` and `Bool` are types, so they themselves typecheck as sorts.
example :
    Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg 5 Γ0 tyNat =
      some (.sort (.succ .zero)) := by
  native_decide

end Phase12

namespace Phase13

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.DefEq
open HeytingLean.LoF.LeanKernel.WHNF
open HeytingLean.LoF.LeanKernel.Infer
open HeytingLean.LoF.LeanKernel.Environment

abbrev E : Type := Expr Nat Unit Unit Unit
abbrev U : Type := ULevel Unit Unit

def cNat : Nat := 100
def cBool : Nat := 101
def cTrue : Nat := 102
def cZero : Nat := 103
def cPiNatNat : Nat := 104
def cIdNatDef : Nat := 105

def tyNat : E := .const cNat []
def tyBool : E := .const cBool []

def piNatNat : E := .forallE 0 .default tyNat tyNat
def idNatVal : E := .lam 0 .default tyNat (.bvar 0)

def env : Environment.Env Nat Unit Unit Unit :=
  { beqName := fun a b => decide (a = b)
    consts :=
      [ ConstDecl.ofType (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cNat (.sort (.succ .zero))
      , ConstDecl.ofType (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cBool (.sort (.succ .zero))
      , ConstDecl.ofType (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cTrue tyBool
      , ConstDecl.ofType (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cZero tyNat
      -- A constant whose value is a Π-type: unfolding is required to expose the `forallE` head.
      , ConstDecl.ofDef (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cPiNatNat (.sort (.succ .zero)) piNatNat
      -- A constant whose type is *defined* via `cPiNatNat`.
      , { name := cIdNatDef, type := fun _ => .const cPiNatNat [], value? := some (fun _ => idNatVal) } ]
    litType? :=
      fun
        | .natVal _ => some tyNat
        | .strVal _ => none }

def rules : Inductive.IotaRules Nat := Environment.Env.iotaRules (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env

def constValue? : Nat → List U → Option E :=
  fun c us => Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env c us

def cfg : Infer.Config Nat Unit Unit Unit :=
  Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env

def Γ0 : Infer.Ctx Nat Unit Unit Unit := Infer.Ctx.empty

-- WHNF δ-reduction: unfold a constant.
example :
    WHNF.whnfWithDelta (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) constValue? rules 1 (.const cPiNatNat []) =
      piNatNat := by
  native_decide

-- DefEq needs δ-reduction to relate a constant to its value.
example :
    DefEq.isDefEqWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules 5 (.const cPiNatNat []) piNatNat =
      false := by
  native_decide

example :
    DefEq.isDefEqWithDelta (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) constValue? rules 5 (.const cPiNatNat []) piNatNat =
      true := by
  native_decide

-- Inference uses δ-reduction on the function type to expose the Π-head at application.
example :
    Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg 40 Γ0 (.app (.const cIdNatDef []) (.lit (.natVal 3))) =
      some tyNat := by
  native_decide

end Phase13

namespace Phase14

open HeytingLean.LoF.LeanKernel
open HeytingLean.LoF.LeanKernel.Lean4LeanSKY

abbrev E : Type := Expr Nat Unit Unit Unit

-- Compile + decode constructor tags through actual SKY reduction.
example :
    (do
      let t <- Lean4LeanSKY.Enc.compileExprNatUnit? (.lit (.natVal 7) : E)
      Lean4LeanSKY.Decode.exprTagFuel 5000 t) =
      some "lit" := by
  native_decide

example :
    (do
      let t <- Lean4LeanSKY.Enc.compileExprNatUnit? (.forallE 0 .default (.const 100 []) (.const 100 []) : E)
      Lean4LeanSKY.Decode.exprTagFuel 5000 t) =
      some "forallE" := by
  native_decide

example :
    (do
      let t <- Lean4LeanSKY.Enc.compileULevelNatUnit? (.imax (.succ .zero) .zero)
      Lean4LeanSKY.Decode.ulevelTagFuel 5000 t) =
      some "imax" := by
  native_decide

-- Produce bounded machine images for later FPGA demos.
example :
    (Lean4LeanSKY.Machine.compileCombToState? (maxNodes := 2) (.app .K .S)).isNone = true := by
  native_decide

example :
    (Lean4LeanSKY.Machine.compileCombToState? (maxNodes := 10) (.app .K .S)).isSome = true := by
  native_decide

example :
    (Lean4LeanSKY.Machine.compileExprToState? (maxNodes := 500) (.lit (.natVal 3) : E)).isSome = true := by
  native_decide

end Phase14

end HeytingLean.Tests.LeanKernelSanity
