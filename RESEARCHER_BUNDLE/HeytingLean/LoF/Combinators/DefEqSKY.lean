import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.WHNFSKY

/-!
# LeanKernel.DefEqSKY (Phase 17)

Computation-plane bridge for fuel-bounded definitional equality:

* define `isDefEq` (Phase 10, β/ζ + WHNF + structural comparison) as an untyped λ term,
* compile it to closed SKY combinators via bracket abstraction (Phase 2),
* run it with `SKYExec.reduceFuel`.

This phase is deliberately **minimal**:
- no δ-unfolding of constants,
- no ι-reduction rules,
- no metavariable assignment / unification constraints.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

namespace DefEqSKY

open HeytingLean.LoF.LeanKernel.WHNFSKY
open HeytingLean.LoF.LeanKernel.WHNFSKY.L

abbrev L : Type := WHNFSKY.L

/-! ## List/Option helpers (Scott) -/

def listCase (xs onNil onCons : L) : L :=
  app2 xs onNil onCons

def boolAnd : L :=
  lam2 "p" "q" (app2 (v "p") (v "q") fls)

/-! ## Universe levels inside SKY -/

def ulevelCase (u cZero cSucc cMax cIMax cParam cMVar : L) : L :=
  app6 u cZero cSucc cMax cIMax cParam cMVar

def natMax (a b : L) : L :=
  app2 (app2 natLt a b) b a

def ulevelIsClosed : L :=
  app .Y <|
    lam "self" <|
      lam "u" <|
        ulevelCase (v "u")
          tru
          (lam "u1" (app (v "self") (v "u1")))
          (lam "a" (lam "b" (app2 boolAnd (app (v "self") (v "a")) (app (v "self") (v "b")))))
          (lam "a" (lam "b" (app2 boolAnd (app (v "self") (v "a")) (app (v "self") (v "b")))))
          (lam "p" fls)
          (lam "m" fls)

def ulevelEval0 : L :=
  app .Y <|
    lam "self" <|
      lam "u" <|
        ulevelCase (v "u")
          natZero
          (lam "u1" (natSucc (app (v "self") (v "u1"))))
          (lam "a" (lam "b" (natMax (app (v "self") (v "a")) (app (v "self") (v "b")))))
          (lam "a"
            (lam "b"
              (let vb := app (v "self") (v "b")
               app2 (app2 natEq vb natZero)
                 natZero
                 (natMax (app (v "self") (v "a")) vb))))
          (lam "p" natZero)
          (lam "m" natZero)

def ulevelEq : L :=
  app .Y <|
    lam "self" <|
      lam "u" <|
        lam "v" <|
          ulevelCase (v "u")
            (ulevelCase (v "v")
              tru
              (lam "v1" fls)
              (lam "a" (lam "b" fls))
              (lam "a" (lam "b" fls))
              (lam "p" fls)
              (lam "m" fls))
            (lam "u1"
              (ulevelCase (v "v")
                fls
                (lam "v1" (app2 (v "self") (v "u1") (v "v1")))
                (lam "a" (lam "b" fls))
                (lam "a" (lam "b" fls))
                (lam "p" fls)
                (lam "m" fls)))
            (lam "ua"
              (lam "ub"
                (ulevelCase (v "v")
                  fls
                  (lam "v1" fls)
                  (lam "va"
                    (lam "vb"
                      (app2 boolAnd
                        (app2 (v "self") (v "ua") (v "va"))
                        (app2 (v "self") (v "ub") (v "vb")))))
                  (lam "a" (lam "b" fls))
                  (lam "p" fls)
                  (lam "m" fls))))
            (lam "ua"
              (lam "ub"
                (ulevelCase (v "v")
                  fls
                  (lam "v1" fls)
                  (lam "a" (lam "b" fls))
                  (lam "va"
                    (lam "vb"
                      (app2 boolAnd
                        (app2 (v "self") (v "ua") (v "va"))
                        (app2 (v "self") (v "ub") (v "vb")))))
                  (lam "p" fls)
                  (lam "m" fls))))
            (lam "up"
              (ulevelCase (v "v")
                fls fls
                (lam "a" (lam "b" fls))
                (lam "a" (lam "b" fls))
                (lam "vp" (app2 natEq (v "up") (v "vp")))
                (lam "m" fls)))
            (lam "um"
              (ulevelCase (v "v")
                fls fls
                (lam "a" (lam "b" fls))
                (lam "a" (lam "b" fls))
                (lam "p" fls)
                (lam "vm" tru)))

def ulevelDefEq : L :=
  lam2 "u" "v" <|
    (let cu := app ulevelIsClosed (v "u")
     let cv := app ulevelIsClosed (v "v")
     app2 (app2 boolAnd cu cv)
       (app2 natEq (app ulevelEval0 (v "u")) (app ulevelEval0 (v "v")))
       (app2 ulevelEq (v "u") (v "v")))

def ulevelListDefEq : L :=
  app .Y <|
    lam "self" <|
      lam "us" <|
        lam "vs" <|
          listCase (v "us")
            (listCase (v "vs") tru (lam "vhd" (lam "vtl" fls)))
            (lam "uhd"
              (lam "utl"
                (listCase (v "vs")
                  fls
                  (lam "vhd"
                    (lam "vtl"
                      (app2 boolAnd
                        (app2 ulevelDefEq (v "uhd") (v "vhd"))
                        (app2 (v "self") (v "utl") (v "vtl"))))))))

/-! ## Literals and expression equality (fuel=0 fallback) -/

def litCase (l onNat onStr : L) : L :=
  app2 l onNat onStr

def litEq : L :=
  lam2 "l1" "l2" <|
    litCase (v "l1")
      (lam "n1"
        (litCase (v "l2")
          (lam "n2" (app2 natEq (v "n1") (v "n2")))
          (lam "s2" fls)))
      (lam "s1"
        (litCase (v "l2")
          (lam "n2" fls)
          (lam "s2" tru)))

def exprEq : L :=
  app .Y <|
    lam "self" <|
      lam "e1" <|
        lam "e2" <|
          exprCase (v "e1")
            (lam "i"
              (exprCase (v "e2")
                (lam "j" (app2 natEq (v "i") (v "j")))
                (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                (lam "f" (lam "a" fls))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                (lam "l" fls)))
            (lam "m"
              (exprCase (v "e2")
                (lam "i" fls) (lam "n" tru) (lam "u" fls) (lam "c" (lam "us" fls))
                (lam "f" (lam "a" fls))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                (lam "l" fls)))
            (lam "u1"
              (exprCase (v "e2")
                (lam "i" fls) (lam "m" fls)
                (lam "u2" (app2 ulevelEq (v "u1") (v "u2")))
                (lam "c" (lam "us" fls))
                (lam "f" (lam "a" fls))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                (lam "l" fls)))
            (lam "c1"
              (lam "us1"
                (exprCase (v "e2")
                  (lam "i" fls) (lam "m" fls) (lam "u" fls)
                  (lam "c2"
                    (lam "us2"
                      (app2 boolAnd
                        (app2 natEq (v "c1") (v "c2"))
                        (app2 ulevelListDefEq (v "us1") (v "us2")))))
                  (lam "f" (lam "a" fls))
                  (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                  (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                  (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                  (lam "l" fls))))
            (lam "f1"
              (lam "a1"
                (exprCase (v "e2")
                  (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                  (lam "f2"
                    (lam "a2"
                      (app2 boolAnd
                        (app2 (v "self") (v "f1") (v "f2"))
                        (app2 (v "self") (v "a1") (v "a2")))))
                  (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                  (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                  (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                  (lam "l" fls))))
            (lam "bn1"
              (lam "bi1"
                (lam "ty1"
                  (lam "b1"
                    (exprCase (v "e2")
                      (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                      (lam "f" (lam "a" fls))
                      (lam "bn2"
                        (lam "bi2"
                          (lam "ty2"
                            (lam "b2"
                              (app2 boolAnd
                                (app2 (v "self") (v "ty1") (v "ty2"))
                                (app2 (v "self") (v "b1") (v "b2")))))))
                      (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                      (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                      (lam "l" fls))))))
            (lam "bn1"
              (lam "bi1"
                (lam "ty1"
                  (lam "b1"
                    (exprCase (v "e2")
                      (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                      (lam "f" (lam "a" fls))
                      (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                      (lam "bn2"
                        (lam "bi2"
                          (lam "ty2"
                            (lam "b2"
                              (app2 boolAnd
                                (app2 (v "self") (v "ty1") (v "ty2"))
                                (app2 (v "self") (v "b1") (v "b2")))))))
                      (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                      (lam "l" fls))))))
            (lam "bn1"
              (lam "bi1"
                (lam "ty1"
                  (lam "v1"
                    (lam "b1"
                      (exprCase (v "e2")
                        (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                        (lam "f" (lam "a" fls))
                        (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                        (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                        (lam "bn2"
                          (lam "bi2"
                            (lam "ty2"
                              (lam "v2"
                                (lam "b2"
                                  (app2 boolAnd
                                    (app2 (v "self") (v "ty1") (v "ty2"))
                                    (app2 boolAnd
                                      (app2 (v "self") (v "v1") (v "v2"))
                                      (app2 (v "self") (v "b1") (v "b2")))))))))
                        (lam "l" fls)))))))
            (lam "l1"
              (exprCase (v "e2")
                (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                (lam "f" (lam "a" fls))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                (lam "l2" (app2 litEq (v "l1") (v "l2")))))

/-! ## Definitional equality (Phase 10) as λ term -/

def isDefEqSkyWith (whnf : L) : L :=
  app .Y <|
    lam "self" <|
      lam "fuel" <|
        lam "e1" <|
          lam "e2" <|
            natCase (v "fuel")
              (app2 exprEq (v "e1") (v "e2"))
              (lam "n"
                (let e1' := app2 whnf (natSucc (v "n")) (v "e1")
                 let e2' := app2 whnf (natSucc (v "n")) (v "e2")
                 exprCase e1'
                   (lam "i"
                     (exprCase e2'
                       (lam "j" (app2 natEq (v "i") (v "j")))
                       (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                       (lam "f" (lam "a" fls))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                       (lam "l" fls)))
                   (lam "m"
                     (exprCase e2'
                       (lam "i" fls) (lam "n" tru) (lam "u" fls) (lam "c" (lam "us" fls))
                       (lam "f" (lam "a" fls))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                       (lam "l" fls)))
                   (lam "u1"
                     (exprCase e2'
                       (lam "i" fls) (lam "m" fls)
                       (lam "u2" (app2 ulevelDefEq (v "u1") (v "u2")))
                       (lam "c" (lam "us" fls))
                       (lam "f" (lam "a" fls))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                       (lam "l" fls)))
                   (lam "c1"
                     (lam "us1"
                       (exprCase e2'
                         (lam "i" fls) (lam "m" fls) (lam "u" fls)
                         (lam "c2"
                           (lam "us2"
                             (app2 boolAnd
                               (app2 natEq (v "c1") (v "c2"))
                               (app2 ulevelListDefEq (v "us1") (v "us2")))))
                         (lam "f" (lam "a" fls))
                         (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                         (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                         (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                         (lam "l" fls))))
                   (lam "f1"
                     (lam "a1"
                       (exprCase e2'
                         (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                         (lam "f2"
                           (lam "a2"
                             (app2 boolAnd
                               (app3 (v "self") (v "n") (v "f1") (v "f2"))
                               (app3 (v "self") (v "n") (v "a1") (v "a2")))))
                         (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                         (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                         (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                         (lam "l" fls))))
                   (lam "bn1"
                     (lam "bi1"
                       (lam "ty1"
                         (lam "b1"
                           (exprCase e2'
                             (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                             (lam "f" (lam "a" fls))
                             (lam "bn2"
                               (lam "bi2"
                                 (lam "ty2"
                                   (lam "b2"
                                     (app2 boolAnd
                                       (app3 (v "self") (v "n") (v "ty1") (v "ty2"))
                                       (app3 (v "self") (v "n") (v "b1") (v "b2")))))))
                             (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                             (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                             (lam "l" fls))))))
                   (lam "bn1"
                     (lam "bi1"
                       (lam "ty1"
                         (lam "b1"
                           (exprCase e2'
                             (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                             (lam "f" (lam "a" fls))
                             (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                             (lam "bn2"
                               (lam "bi2"
                                 (lam "ty2"
                                   (lam "b2"
                                     (app2 boolAnd
                                       (app3 (v "self") (v "n") (v "ty1") (v "ty2"))
                                       (app3 (v "self") (v "n") (v "b1") (v "b2")))))))
                             (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                             (lam "l" fls))))))
                   (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                   (lam "l1"
                     (exprCase e2'
                       (lam "i" fls) (lam "m" fls) (lam "u" fls) (lam "c" (lam "us" fls))
                       (lam "f" (lam "a" fls))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "body" fls))))
                       (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" fls)))))
                       (lam "l2" (app2 litEq (v "l1") (v "l2")))))))

def isDefEqSky : L :=
  isDefEqSkyWith WHNFSKY.whnfSky

/-! ## Closed compilation and a tiny execution helper -/

def compileClosed? (t : L) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) t

def isDefEqComb? : Option Comb :=
  compileClosed? isDefEqSky

def encodeNatComb? (n : Nat) : Option Comb :=
  compileClosed? (Expr.Scott.encodeNat n)

def runIsDefEqFuel (fuelDefEq fuelReduce : Nat) (e1 e2 : Expr Nat Unit Unit Unit) : Option Bool := do
  let deq <- isDefEqComb?
  let fuelC <- encodeNatComb? fuelDefEq
  let e1C <- Lean4LeanSKY.Enc.compileExprNatUnit? e1
  let e2C <- Lean4LeanSKY.Enc.compileExprNatUnit? e2
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app deq fuelC) e1C) e2C)
  SKYExec.decodeChurchBoolFuel fuelReduce out

end DefEqSKY

end LeanKernel
end LoF
end HeytingLean
