import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.WHNFSKY
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.InferSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

/-!
# LeanKernel.KernelSKY (Phase 19)

Integration layer for the staged “Lean from LoF” kernel compilation pipeline.

This module bundles the computation-plane SKY programs from:
- Phase 16: `WHNFSKY.whnfSky`
- Phase 17: `DefEqSKY.isDefEqSky`
- Phase 18: `InferSKY.inferSky`

and wires them to the Phase 14 data-plane encoders/decoders (`Lean4LeanSKY`).

The primary deliverable is a cached `Compiled` bundle so later phases / demos can
compile once and run many times.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators

namespace KernelSKY

abbrev E : Type := Expr Nat Unit Unit Unit

/-! ## Shared compilation helpers -/

def encodeNatComb? (n : Nat) : Option Comb :=
  WHNFSKY.encodeNatComb? n

def compileExprNatUnit? (e : E) : Option Comb :=
  Lean4LeanSKY.Enc.compileExprNatUnit? e

/-! ## Cached compilation bundle -/

structure Compiled where
  whnf : Comb
  isDefEq : Comb
  infer : Comb
  check : Comb
  emptyCtx : Comb

def compile? : Option Compiled := do
  let whnf <- WHNFSKY.whnfComb?
  let isDefEq <- DefEqSKY.isDefEqComb?
  let infer <- InferSKY.inferComb?
  let check <- InferSKY.checkComb?
  let emptyCtx <- InferSKY.emptyCtxComb?
  pure { whnf, isDefEq, infer, check, emptyCtx }

/-! ## Running with a cached bundle -/

def runWhnfTagFuelWith (k : Compiled) (fuelWhnf fuelReduce : Nat) (e : E) : Option String := do
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- compileExprNatUnit? e
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app k.whnf fuelC) eC)
  Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

def runWhnfCombFuelWith (k : Compiled) (fuelWhnf fuelReduce : Nat) (e : E) : Option Comb := do
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- compileExprNatUnit? e
  some <| SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app k.whnf fuelC) eC)

def runIsDefEqFuelWith (k : Compiled) (fuelDefEq fuelReduce : Nat) (e1 e2 : E) : Option Bool := do
  let fuelC <- encodeNatComb? fuelDefEq
  let e1C <- compileExprNatUnit? e1
  let e2C <- compileExprNatUnit? e2
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app k.isDefEq fuelC) e1C) e2C)
  SKYExec.decodeChurchBoolFuel fuelReduce out

def runIsDefEqCombFuelWith (k : Compiled) (fuelDefEq fuelReduce : Nat) (e1C e2C : Comb) : Option Bool := do
  let fuelC <- encodeNatComb? fuelDefEq
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app k.isDefEq fuelC) e1C) e2C)
  SKYExec.decodeChurchBoolFuel fuelReduce out

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

def runInferTagFuelWith (k : Compiled) (fuelInfer fuelReduce : Nat) (e : E) : Option String := do
  let fuelC <- encodeNatComb? fuelInfer
  let eC <- compileExprNatUnit? e
  let outOpt := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app k.infer fuelC) k.emptyCtx) eC)
  decodeOptExprTagFuel fuelReduce outOpt

def runInferOptCombFuelWith (k : Compiled) (fuelInfer fuelReduce : Nat) (e : E) : Option Comb := do
  let fuelC <- encodeNatComb? fuelInfer
  let eC <- compileExprNatUnit? e
  some <| SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app k.infer fuelC) k.emptyCtx) eC)

def runCheckFuelWith (k : Compiled) (fuel fuelReduce : Nat) (e ty : E) : Option Bool := do
  let fuelC <- encodeNatComb? fuel
  let eC <- compileExprNatUnit? e
  let tyC <- compileExprNatUnit? ty
  let out :=
    SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app (Comb.app k.check fuelC) k.emptyCtx) eC) tyC)
  SKYExec.decodeChurchBoolFuel fuelReduce out

/-! ## Convenience runners (compile bundle + run once) -/

def runWhnfTagFuel (fuelWhnf fuelReduce : Nat) (e : E) : Option String := do
  let k <- compile?
  runWhnfTagFuelWith k fuelWhnf fuelReduce e

def runIsDefEqFuel (fuelDefEq fuelReduce : Nat) (e1 e2 : E) : Option Bool := do
  let k <- compile?
  runIsDefEqFuelWith k fuelDefEq fuelReduce e1 e2

def runInferTagFuel (fuelInfer fuelReduce : Nat) (e : E) : Option String := do
  let k <- compile?
  runInferTagFuelWith k fuelInfer fuelReduce e

def runCheckFuel (fuel fuelReduce : Nat) (e ty : E) : Option Bool := do
  let k <- compile?
  runCheckFuelWith k fuel fuelReduce e ty

end KernelSKY

end LeanKernel
end LoF
end HeytingLean
