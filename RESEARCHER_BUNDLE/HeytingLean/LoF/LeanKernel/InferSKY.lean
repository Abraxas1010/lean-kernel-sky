import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.WHNFSKY
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

/-!
# LeanKernel.InferSKY (Phase 18)

Computation-plane bridge for fuel-bounded type inference:

* re-express the Phase 12 algorithmic kernel checker (`Infer.infer?`) as an untyped λ term,
* compile it to closed SKY combinators via bracket abstraction (Phase 2),
* run it with `SKYExec.reduceFuel`.

This phase is intentionally **minimal / environment-free**:
- no constant table lookup (`constType?` / `constValue?`) and thus no δ-unfolding,
- no metavariable typing,
- no literal typing.

It is designed to be the executable "core" that later phases can extend by
threading an explicit environment/config through the computation-plane encoding.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

namespace InferSKY

open HeytingLean.LoF.LeanKernel.WHNFSKY
open HeytingLean.LoF.LeanKernel.WHNFSKY.L

abbrev L : Type := WHNFSKY.L

/-! ## Small Scott encodings (List) -/

def listNil : L :=
  lam2 "n" "c" (v "n")

def listCons (hd tl : L) : L :=
  lam2 "n" "c" (app2 (v "c") hd tl)

def listCase (xs onNil onCons : L) : L :=
  app2 xs onNil onCons

/-! `listNth?` for Scott lists: returns `Option α` (Scott) -/
def listNth? : L :=
  app .Y <|
    lam "self" <|
      lam "xs" <|
        lam "i" <|
          natCase (v "i")
            (listCase (v "xs")
              optNone
              (lam "hd" (lam "tl" (optSome (v "hd")))))
            (lam "n"
              (listCase (v "xs")
                optNone
                (lam "hd" (lam "tl" (app2 (v "self") (v "tl") (v "n"))))))

/-! ## Universe-level constructors (Scott encoding) -/

def lam6 (a b c d e f : String) (body : L) : L :=
  lam a (lam b (lam c (lam d (lam e (lam f body)))))

def ulevelSucc (u : L) : L :=
  lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar"
    (app (v "cSucc") u)

def ulevelIMax (a b : L) : L :=
  lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar"
    (app2 (v "cIMax") a b)

/-! ## Context lookup (De Bruijn) -/

def bvarType? : L :=
  lam2 "ctx" "i" <|
    optCase (app2 listNth? (v "ctx") (v "i"))
      optNone
      (lam "ty"
        (optSome
          (app3 shiftBVarSky natZero (natSucc (v "i")) (v "ty"))))

/-! ## Inference (Phase 12) as λ term, parameterized by external kernel hooks -/

def inferSkyWith (constType? whnf isDefEq : L) : L :=
  app .Y <|
    lam "self" <|
      lam "fuel" <|
        lam "ctx" <|
          lam "e" <|
            natCase (v "fuel")
              optNone
              (lam "n"
                (exprCase (v "e")
                  -- bvar
                  (lam "i" (app2 bvarType? (v "ctx") (v "i")))
                  -- mvar (no typing info in the minimal config)
                  (lam "m" optNone)
                  -- sort u : Sort (succ u)
                  (lam "u" (optSome (exprSort (ulevelSucc (v "u")))))
                  -- const (lookup hook)
                  (lam "c" (lam "us" (app2 constType? (v "c") (v "us"))))
                  -- app
                  (lam "f"
                    (lam "a"
                      (optCase (app3 (v "self") (v "n") (v "ctx") (v "f"))
                        optNone
                        (lam "tf"
                          (let tfWhnf := app2 whnf (natSucc (v "n")) (v "tf")
                           exprCase tfWhnf
                             (lam "i" optNone)
                             (lam "m" optNone)
                             (lam "u" optNone)
                             (lam "c" (lam "us" optNone))
                             (lam "f2" (lam "a2" optNone))
                             (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                             (lam "bn"
                               (lam "bi"
                                 (lam "dom"
                                   (lam "body"
                                     (optCase (app3 (v "self") (v "n") (v "ctx") (v "a"))
                                       optNone
                                       (lam "ta"
                                         (app2 (app3 isDefEq (natSucc (v "n")) (v "ta") (v "dom"))
                                           (optSome (app2 instantiate1Sky (v "a") (v "body")))
                                           optNone)))))))
                             (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                             (lam "l" optNone))))))
                  -- lam
                  (lam "bn"
                    (lam "bi"
                      (lam "ty"
                        (lam "body"
                          (optCase (app3 (v "self") (v "n") (v "ctx") (v "ty"))
                            optNone
                            (lam "tyTy"
                              (exprCase (v "tyTy")
                                (lam "i" optNone)
                                (lam "m" optNone)
                                (lam "u"
                                  (let ctx' := listCons (v "ty") (v "ctx")
                                   optCase (app3 (v "self") (v "n") ctx' (v "body"))
                                     optNone
                                     (lam "bodyTy"
                                       (optSome (exprForall (v "bn") (v "bi") (v "ty") (v "bodyTy"))))))
                                (lam "c" (lam "us" optNone))
                                (lam "f" (lam "a" optNone))
                                (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                                (lam "l" optNone))))))))
                  -- forallE
                  (lam "bn"
                    (lam "bi"
                      (lam "ty"
                        (lam "body"
                          (optCase (app3 (v "self") (v "n") (v "ctx") (v "ty"))
                            optNone
                            (lam "tyTy"
                              (exprCase (v "tyTy")
                                (lam "i" optNone)
                                (lam "m" optNone)
                                (lam "u"
                                  (let ctx' := listCons (v "ty") (v "ctx")
                                   optCase (app3 (v "self") (v "n") ctx' (v "body"))
                                     optNone
                                     (lam "bodyTy"
                                       (exprCase (v "bodyTy")
                                         (lam "i" optNone)
                                         (lam "m" optNone)
                                         (lam "v" (optSome (exprSort (ulevelIMax (v "u") (v "v")))))
                                         (lam "c" (lam "us" optNone))
                                         (lam "f" (lam "a" optNone))
                                         (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                         (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                         (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                                         (lam "l" optNone)))))
                                (lam "c" (lam "us" optNone))
                                (lam "f" (lam "a" optNone))
                                (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                                (lam "l" optNone))))))))
                  -- letE
                  (lam "bn"
                    (lam "bi"
                      (lam "ty"
                        (lam "val"
                          (lam "body"
                            (optCase (app3 (v "self") (v "n") (v "ctx") (v "ty"))
                              optNone
                              (lam "tyTy"
                                (exprCase (v "tyTy")
                                  (lam "i" optNone)
                                  (lam "m" optNone)
                                  (lam "u"
                                    (optCase (app3 (v "self") (v "n") (v "ctx") (v "val"))
                                      optNone
                                      (lam "tVal"
                                        (app2 (app3 isDefEq (natSucc (v "n")) (v "tVal") (v "ty"))
                                          (let ctx' := listCons (v "ty") (v "ctx")
                                           optCase (app3 (v "self") (v "n") ctx' (v "body"))
                                             optNone
                                             (lam "bodyTy"
                                               (optSome (app2 instantiate1Sky (v "val") (v "bodyTy")))))
                                          optNone))))
                                  (lam "c" (lam "us" optNone))
                                  (lam "f" (lam "a" optNone))
                                  (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                  (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                                  (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                                  (lam "l" optNone)))))))))
                  -- lit
                  (lam "l" optNone)))

/-! A boolean wrapper, mirroring `Infer.check`. -/
def checkSkyWith (constType? whnf isDefEq : L) : L :=
  lam4 "fuel" "ctx" "e" "ty" <|
    optCase (app3 (inferSkyWith constType? whnf isDefEq) (v "fuel") (v "ctx") (v "e"))
      fls
      (lam "ty'" (app3 isDefEq (v "fuel") (v "ty'") (v "ty")))

/-! ## Minimal (environment-free) specializations used by Phase 18 -/

def constTypeNone : L :=
  lam2 "c" "us" optNone

def inferSky : L :=
  inferSkyWith constTypeNone WHNFSKY.whnfSky DefEqSKY.isDefEqSky

def checkSky : L :=
  checkSkyWith constTypeNone WHNFSKY.whnfSky DefEqSKY.isDefEqSky

/-! ## Closed compilation and a tiny execution helper -/

def compileClosed? (t : L) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) t

def inferComb? : Option Comb :=
  compileClosed? inferSky

def checkComb? : Option Comb :=
  compileClosed? checkSky

def encodeNatComb? (n : Nat) : Option Comb :=
  compileClosed? (Expr.Scott.encodeNat n)

def emptyCtxComb? : Option Comb :=
  compileClosed? listNil

def runInferTagFuel (fuelInfer fuelReduce : Nat) (e : Expr Nat Unit Unit Unit) : Option String := do
  let infer <- inferComb?
  let fuelC <- encodeNatComb? fuelInfer
  let ctxC <- emptyCtxComb?
  let eC <- Lean4LeanSKY.Enc.compileExprNatUnit? e
  let outOpt := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app infer fuelC) ctxC) eC)
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app outOpt Comb.K) Comb.I)
  if out = Comb.K then
    none
  else
    Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

def runCheckFuel (fuel fuelReduce : Nat) (e ty : Expr Nat Unit Unit Unit) : Option Bool := do
  let chk <- checkComb?
  let fuelC <- encodeNatComb? fuel
  let ctxC <- emptyCtxComb?
  let eC <- Lean4LeanSKY.Enc.compileExprNatUnit? e
  let tyC <- Lean4LeanSKY.Enc.compileExprNatUnit? ty
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app (Comb.app chk fuelC) ctxC) eC) tyC)
  SKYExec.decodeChurchBoolFuel fuelReduce out

end InferSKY

end LeanKernel
end LoF
end HeytingLean
