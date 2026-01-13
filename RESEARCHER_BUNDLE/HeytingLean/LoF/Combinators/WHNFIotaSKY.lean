import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.Inductive
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.WHNFSKY

/-!
# LeanKernel.WHNFIotaSKY (Phase 23)

Computation-plane ι-reduction (`casesOn`/recursor reduction) for weak-head normalization:

* encode a small, data-driven `IotaRules` structure as Scott data accessible from SKY,
* implement one ι-step (`iotaStepSky`) mirroring `Inductive.iotaStep?` (Phase 11),
* integrate ι into a β/ζ WHNF step (`whnfStepIotaSky`) and bounded WHNF (`whnfIotaSky`),
* compile to closed SKY combinators via bracket abstraction and execute via `SKYExec.reduceFuel`.

This phase is specialized to `Name := Nat` for demo/cross-validation (name equality uses `natEq`).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

namespace WHNFIotaSKY

open HeytingLean.LoF.LeanKernel.WHNFSKY
open HeytingLean.LoF.LeanKernel.WHNFSKY.L

abbrev L : Type := WHNFSKY.L

/-! ## Small Scott encodings (List, Pair) -/

def listNil : L :=
  lam2 "n" "c" (v "n")

def listCons (hd tl : L) : L :=
  lam2 "n" "c" (app2 (v "c") hd tl)

def listCase (xs onNil onCons : L) : L :=
  app2 xs onNil onCons

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

def listLength : L :=
  app .Y <|
    lam "self" <|
      lam "xs" <|
        listCase (v "xs")
          natZero
          (lam "hd" (lam "tl" (natSucc (app (v "self") (v "tl")))))

def listGetLast? : L :=
  app .Y <|
    lam "self" <|
      lam "xs" <|
        listCase (v "xs")
          optNone
          (lam "hd" <|
            lam "tl" <|
              listCase (v "tl")
                (optSome (v "hd"))
                (lam "hd2" (lam "tl2" (app (v "self") (v "tl")))))

def pair (a b : L) : L :=
  lam "p" (app2 (v "p") a b)

def pairCase (p k : L) : L :=
  app p k

/-! ## Scott data encodings for ι rules -/

def ctorSpecEncode (name numFields : L) : L :=
  lam "c" (app2 (v "c") name numFields)

def casesOnSpecEncode (recursor numParams ctors : L) : L :=
  lam "c" (app3 (v "c") recursor numParams ctors)

def iotaRulesEncode (specs : L) : L :=
  lam "c" (app (v "c") specs)

def iotaRulesSpecs (rules : L) : L :=
  app rules (lam "s" (v "s"))

/-! ## Application spine utilities (`getAppFnArgs`, `mkAppN`) -/

def getAppFnArgsGoSky : L :=
  app .Y <|
    lam "self" <|
      lam "e" <|
        lam "args" <|
          exprCase (v "e")
            (lam "i" (pair (v "e") (v "args")))
            (lam "m" (pair (v "e") (v "args")))
            (lam "u" (pair (v "e") (v "args")))
            (lam "c" (lam "us" (pair (v "e") (v "args"))))
            (lam "f" (lam "a" (app2 (v "self") (v "f") (listCons (v "a") (v "args")))))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" (pair (v "e") (v "args"))))))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" (pair (v "e") (v "args"))))))
            (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" (pair (v "e") (v "args")))))))
            (lam "l" (pair (v "e") (v "args")))

def getAppFnArgsSky : L :=
  lam "e" (app2 getAppFnArgsGoSky (v "e") listNil)

def mkAppNSky : L :=
  app .Y <|
    lam "self" <|
      lam "f" <|
        lam "args" <|
          listCase (v "args")
            (v "f")
            (lam "hd" (lam "tl" (app2 (v "self") (exprApp (v "f") (v "hd")) (v "tl"))))

/-! ## Lookup helpers (casesOn spec, ctor index/arity) -/

def lookupCasesOnSpec : L :=
  app .Y <|
    lam "self" <|
      lam "specs" <|
        lam "recursor" <|
          listCase (v "specs")
            optNone
            (lam "spec" <|
              lam "rest" <|
                app (v "spec") <|
                  lam "r" <|
                    lam "np" <|
                      lam "ctors" <|
                        app2 (app2 natEq (v "r") (v "recursor"))
                          (optSome (v "spec"))
                          (app2 (v "self") (v "rest") (v "recursor")))

def ctorIndex? : L :=
  let go :=
    app .Y <|
      lam "self" <|
        lam "ctors" <|
          lam "name" <|
            lam "i" <|
              listCase (v "ctors")
                optNone
                (lam "ctor" <|
                  lam "rest" <|
                    app (v "ctor") <|
                      lam "ctorName" <|
                        lam "arity" <|
                          app2 (app2 natEq (v "ctorName") (v "name"))
                            (optSome (v "i"))
                            (app3 (v "self") (v "rest") (v "name") (natSucc (v "i"))))
  lam2 "ctors" "name" (app3 go (v "ctors") (v "name") natZero)

def ctorArity? : L :=
  lam2 "ctors" "idx" <|
    optCase (app2 listNth? (v "ctors") (v "idx"))
      optNone
      (lam "ctor" <|
        app (v "ctor") <|
          lam "ctorName" <|
            lam "arity" <|
              optSome (v "arity"))

/-! ## ι-step (casesOn reduction) -/

/--
One ι-reduction step using Scott-encoded rules:

`iotaStepSky : IotaRules → Expr → Option Expr`.
-/
def iotaStepSky : L :=
  lam2 "rules" "e" <|
    let specs := iotaRulesSpecs (v "rules")

    let onMajor : L :=
      lam "numParams" <|
        lam "ctors" <|
          lam "args" <|
            optCase (app listGetLast? (v "args"))
              optNone
              (lam "major"
                (pairCase (app getAppFnArgsSky (v "major"))
                  (lam "majorFn"
                    (lam "majorArgs"
                      (exprCase (v "majorFn")
                        (lam "i" optNone)
                        (lam "m" optNone)
                        (lam "u" optNone)
                        (lam "ctorName"
                          (lam "ctorUs"
                            (optCase (app2 ctorIndex? (v "ctors") (v "ctorName"))
                              optNone
                              (lam "idx"
                                (optCase (app2 ctorArity? (v "ctors") (v "idx"))
                                  optNone
                                  (lam "arity"
                                    (let majorLen := app listLength (v "majorArgs");
                                     app2 (app2 natEq majorLen (v "arity"))
                                       (let minorIdx := app2 natAdd (v "numParams") (v "idx");
                                        optCase (app2 listNth? (v "args") minorIdx)
                                          optNone
                                          (lam "minor"
                                            (optSome (app2 mkAppNSky (v "minor") (v "majorArgs")))))
                                       optNone)))))))
                        (lam "f" (lam "a" optNone))
                        (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                        (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                        (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                        (lam "l" optNone))))))

    let onSpec : L :=
      lam "spec" <|
        app (v "spec")
          (lam "r"
            (lam "numParams"
              (lam "ctors"
                (lam "args"
                  (let expected := natSucc (app2 natAdd (v "numParams") (app listLength (v "ctors")));
                   let argsLen := app listLength (v "args");
                   app2 (app2 natEq argsLen expected) (app3 onMajor (v "numParams") (v "ctors") (v "args")) optNone)))))

    pairCase (app getAppFnArgsSky (v "e"))
      (lam "fn"
        (lam "args"
          (exprCase (v "fn")
            (lam "i" optNone)
            (lam "m" optNone)
            (lam "u" optNone)
            (lam "c"
              (lam "us"
                (optCase (app2 lookupCasesOnSpec specs (v "c"))
                  optNone
                  (lam "spec" (app2 onSpec (v "spec") (v "args"))))))
            (lam "f" (lam "a" optNone))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
            (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
            (lam "l" optNone))))

/-! ## WHNF with ι (β/ζ/ι, left spine) -/

def whnfStepIotaSky : L :=
  app .Y <|
    lam "self" <|
      lam "rules" <|
        lam "e" <|
          exprCase (v "e")
            (lam "i" optNone)
            (lam "m" optNone)
            (lam "u" optNone)
            (lam "c" (lam "us" optNone))
            (lam "f"
              (lam "a"
                (optCase (app2 iotaStepSky (v "rules") (exprApp (v "f") (v "a")))
                  (optCase (app2 (v "self") (v "rules") (v "f"))
                    (exprCase (v "f")
                      (lam "i" optNone)
                      (lam "m" optNone)
                      (lam "u" optNone)
                      (lam "c" (lam "us" optNone))
                      (lam "f1" (lam "a1" optNone))
                      (lam "bn"
                        (lam "bi"
                          (lam "ty"
                            (lam "body" (optSome (app2 instantiate1Sky (v "a") (v "body")))))))
                      (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
                      (lam "bn" (lam "bi" (lam "ty" (lam "val" (lam "body" optNone)))))
                      (lam "l" optNone))
                    (lam "f'" (optSome (exprApp (v "f'") (v "a")))))
                  (lam "e'" (optSome (v "e'"))))))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
            (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
            (lam "bn"
              (lam "bi"
                (lam "ty"
                  (lam "val"
                    (lam "body" (optSome (app2 instantiate1Sky (v "val") (v "body"))))))))
            (lam "l" optNone)

def whnfIotaSky : L :=
  app .Y
    (lam "self"
      (lam "rules"
        (lam "fuel"
          (lam "e"
            (natCase (v "fuel")
              (v "e")
              (lam "n"
                (optCase (app2 whnfStepIotaSky (v "rules") (v "e"))
                  (v "e")
                  (lam "e'" (app3 (v "self") (v "rules") (v "n") (v "e'"))))))))))

/-! ## Closed compilation and runners -/

def compileClosed? (t : L) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) t

def whnfIotaComb? : Option Comb :=
  compileClosed? whnfIotaSky

def encodeNatComb? (n : Nat) : Option Comb :=
  compileClosed? (Expr.Scott.encodeNat n)

namespace Enc

def nat : Nat → L := Expr.Scott.encodeNat

def ctorSpec (name numFields : Nat) : L :=
  ctorSpecEncode (nat name) (nat numFields)

def casesOnSpec (recursor numParams : Nat) (ctors : List (Nat × Nat)) : L :=
  let rec go : List (Nat × Nat) → L
    | [] => listNil
    | (c, a) :: cs => listCons (ctorSpec c a) (go cs)
  casesOnSpecEncode (nat recursor) (nat numParams) (go ctors)

def iotaRules (specs : List L) : L :=
  let rec go : List L → L
    | [] => listNil
    | s :: ss => listCons s (go ss)
  iotaRulesEncode (go specs)

end Enc

def runWhnfIotaTagFuel (fuelWhnf fuelReduce : Nat) (rules : L) (e : Expr Nat Unit Unit Unit) : Option String := do
  let whnf <- whnfIotaComb?
  let rulesC <- compileClosed? rules
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- Lean4LeanSKY.Enc.compileExprNatUnit? e
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app (Comb.app whnf rulesC) fuelC) eC)
  Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

end WHNFIotaSKY

end LeanKernel
end LoF
end HeytingLean
