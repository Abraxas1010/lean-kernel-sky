import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.WHNFDeltaSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.InferSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

/-!
# LeanKernel.FullKernelSKY (Phase 24)

Integration bundle for the “computation plane” kernel that combines:
- β/ζ WHNF (Phase 16),
- δ-reduction via an encoded constant environment (Phase 22 + Phase 21),
- ι-reduction via encoded `casesOn` rules (Phase 23),
- definitional equality (Phase 17) and inference/checking (Phase 18) parameterized by the full WHNF.

This module mirrors `KernelSKY` (Phase 19) but adds explicit `env` and `rules`
arguments (both Scott-encoded data accessible from SKY).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators

namespace FullKernelSKY

open HeytingLean.LoF.LeanKernel.WHNFSKY
open HeytingLean.LoF.LeanKernel.WHNFSKY.L

abbrev L : Type := WHNFSKY.L
abbrev E : Type := Expr Nat Unit Unit Unit

/-! ## Full WHNF (β/ζ/δ/ι) as a λ term -/

def whnfStepFullSky : L :=
  lam3 "env" "rules" "e" <|
    optCase (app2 WHNFIotaSKY.iotaStepSky (v "rules") (v "e"))
      (app2 WHNFDeltaSKY.whnfStepDeltaSky (v "env") (v "e"))
      (lam "e'" (optSome (v "e'")))

def whnfFullSky : L :=
  app .Y <|
    lam "self" <|
      lam "env" <|
        lam "rules" <|
          lam "fuel" <|
            lam "e" <|
              natCase (v "fuel")
                (v "e")
                (lam "n" <|
                  optCase (app3 whnfStepFullSky (v "env") (v "rules") (v "e"))
                    (v "e")
                    (lam "e'"
                      (app4 (v "self") (v "env") (v "rules") (v "n") (v "e'"))))

/-! ## Hooks to parameterize Phase 17/18 algorithms -/

def constTypeFromEnv : L :=
  /- `InferSKY.inferSkyWith` expects `constType? : Name → List ULevel → Option Expr`.
     The Phase 21 environment is already instantiated at a fixed `us`, so we ignore the `us` argument. -/
  lam3 "env" "c" "us" (app2 EnvironmentSKY.constType? (v "env") (v "c"))

def whnfFromEnvRules : L :=
  /- A closure `fuel → Expr → Expr` capturing `env` and `rules`. -/
  lam2 "env" "rules" <|
    lam2 "fuel" "e" (app4 whnfFullSky (v "env") (v "rules") (v "fuel") (v "e"))

def isDefEqFullSky : L :=
  lam2 "env" "rules" <|
    DefEqSKY.isDefEqSkyWith (app2 whnfFromEnvRules (v "env") (v "rules"))

def inferFullSky : L :=
  lam2 "env" "rules" <|
    let whnf := app2 whnfFromEnvRules (v "env") (v "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := app constTypeFromEnv (v "env")
    InferSKY.inferSkyWith constType? whnf isDefEq

def checkFullSky : L :=
  lam2 "env" "rules" <|
    let whnf := app2 whnfFromEnvRules (v "env") (v "rules")
    let isDefEq := DefEqSKY.isDefEqSkyWith whnf
    let constType? := app constTypeFromEnv (v "env")
    InferSKY.checkSkyWith constType? whnf isDefEq

/-! ## Closed compilation bundle -/

def compileClosed? (t : L) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) t

def whnfFullComb? : Option Comb :=
  compileClosed? whnfFullSky

def isDefEqFullComb? : Option Comb :=
  compileClosed? isDefEqFullSky

def inferFullComb? : Option Comb :=
  compileClosed? inferFullSky

def checkFullComb? : Option Comb :=
  compileClosed? checkFullSky

def emptyEnvComb? : Option Comb :=
  compileClosed? EnvironmentSKY.envEmpty

def emptyRulesComb? : Option Comb :=
  compileClosed? (WHNFIotaSKY.Enc.iotaRules [])

structure FullCompiled where
  whnf : Comb
  isDefEq : Comb
  infer : Comb
  check : Comb
  emptyCtx : Comb
  emptyEnv : Comb
  emptyRules : Comb

def compileFull? : Option FullCompiled := do
  let whnf <- whnfFullComb?
  let isDefEq <- isDefEqFullComb?
  let infer <- inferFullComb?
  let check <- checkFullComb?
  let emptyCtx <- InferSKY.emptyCtxComb?
  let emptyEnv <- emptyEnvComb?
  let emptyRules <- emptyRulesComb?
  pure { whnf, isDefEq, infer, check, emptyCtx, emptyEnv, emptyRules }

/-! ## Runners (fuel-bounded, decoding only tags/bools) -/

def encodeNatComb? (n : Nat) : Option Comb :=
  WHNFSKY.encodeNatComb? n

def compileExprNatUnit? (e : E) : Option Comb :=
  Lean4LeanSKY.Enc.compileExprNatUnit? e

def decodeOptExprTagFuel (fuelReduce : Nat) (optExpr : Comb) : Option String :=
  /-
  Scott `Option α` is `λ n s => ...`. When we apply it to `K` and `I`,
  `none` reduces to `K` and `some x` reduces to `x`.
  -/
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app optExpr Comb.K) Comb.I)
  if out = Comb.K then
    none
  else
    Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

def decodeOptExprCombFuel (fuelReduce : Nat) (optExpr : Comb) : Option Comb :=
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app optExpr Comb.K) Comb.I)
  if out = Comb.K then
    none
  else
    some out

def runWhnfFullTagFuelWith (k : FullCompiled) (fuelWhnf fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option String := do
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- compileExprNatUnit? e
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app k.whnf envC) rulesC) fuelC) eC
  Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

def runWhnfFullCombFuelWith (k : FullCompiled) (fuelWhnf fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option Comb := do
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- compileExprNatUnit? e
  some <|
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app k.whnf envC) rulesC) fuelC) eC

def runIsDefEqFullFuelWith (k : FullCompiled) (fuelDefEq fuelReduce : Nat)
    (envC rulesC : Comb) (e1 e2 : E) : Option Bool := do
  let fuelC <- encodeNatComb? fuelDefEq
  let e1C <- compileExprNatUnit? e1
  let e2C <- compileExprNatUnit? e2
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.isDefEq envC) rulesC) fuelC) e1C) e2C
  SKYExec.decodeChurchBoolFuel fuelReduce out

def runIsDefEqFullCombFuelWith (k : FullCompiled) (fuelDefEq fuelReduce : Nat)
    (envC rulesC e1C e2C : Comb) : Option Bool := do
  let fuelC <- encodeNatComb? fuelDefEq
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.isDefEq envC) rulesC) fuelC) e1C) e2C
  SKYExec.decodeChurchBoolFuel fuelReduce out

def runInferFullTagFuelWith (k : FullCompiled) (fuelInfer fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option String := do
  let fuelC <- encodeNatComb? fuelInfer
  let eC <- compileExprNatUnit? e
  let outOpt :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.infer envC) rulesC) fuelC) k.emptyCtx) eC
  decodeOptExprTagFuel fuelReduce outOpt

def runInferFullOptCombFuelWith (k : FullCompiled) (fuelInfer fuelReduce : Nat)
    (envC rulesC : Comb) (e : E) : Option Comb := do
  let fuelC <- encodeNatComb? fuelInfer
  let eC <- compileExprNatUnit? e
  some <|
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.infer envC) rulesC) fuelC) k.emptyCtx) eC

def runCheckFullFuelWith (k : FullCompiled) (fuel fuelReduce : Nat)
    (envC rulesC : Comb) (e ty : E) : Option Bool := do
  let fuelC <- encodeNatComb? fuel
  let eC <- compileExprNatUnit? e
  let tyC <- compileExprNatUnit? ty
  let out :=
    SKYExec.reduceFuel fuelReduce <|
      Comb.app (Comb.app (Comb.app (Comb.app (Comb.app (Comb.app k.check envC) rulesC) fuelC) k.emptyCtx) eC) tyC
  SKYExec.decodeChurchBoolFuel fuelReduce out

end FullKernelSKY

end LeanKernel
end LoF
end HeytingLean
