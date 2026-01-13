import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

/-!
# LeanKernel.WHNFSKY (Phase 16)

Computation-plane bridge for weak-head normalization:

* define WHNF (β/ζ, left spine) as an untyped λ term (`Bracket.Lam`),
* compile it to closed SKY combinators via bracket abstraction (Phase 2),
* run it with a fuel-bounded reducer (`SKYExec.reduceFuel`).

This phase is intentionally "environment-free": it matches `WHNF.whnf` which does
not perform δ-unfolding of `const` nodes.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

namespace WHNFSKY

abbrev L : Type := Bracket.Lam String

namespace L

def v (s : String) : L := Bracket.Lam.var s
def app (f a : L) : L := Bracket.Lam.app f a
def lam (x : String) (body : L) : L := Bracket.Lam.lam x body

def app2 (f a b : L) : L := app (app f a) b
def app3 (f a b c : L) : L := app (app2 f a b) c
def app4 (f a b c d : L) : L := app (app3 f a b c) d
def app5 (f a b c d e : L) : L := app (app4 f a b c d) e
def app6 (f a b c d e g : L) : L := app (app5 f a b c d e) g
def app7 (f a b c d e g h : L) : L := app (app6 f a b c d e g) h
def app8 (f a b c d e g h i : L) : L := app (app7 f a b c d e g h) i
def app9 (f a b c d e g h i j : L) : L := app (app8 f a b c d e g h i) j

def lam2 (x y : String) (body : L) : L := lam x (lam y body)
def lam3 (x y z : String) (body : L) : L := lam x (lam y (lam z body))
def lam4 (a b c d : String) (body : L) : L := lam a (lam b (lam c (lam d body)))
def lam9 (a b c d e f g h i : String) (body : L) : L :=
  lam a (lam b (lam c (lam d (lam e (lam f (lam g (lam h (lam i body))))))))

end L

open L

/-! ## Small Scott encodings (Bool/Option/Nat) -/

def I : L :=
  app2 (.S) (.K) (.K)

def tru : L := .K
def fls : L := app (.K) I

def optNone : L :=
  lam2 "n" "s" (v "n")

def optSome (x : L) : L :=
  lam2 "n" "s" (app (v "s") x)

def optCase (o onNone onSome : L) : L :=
  app2 o onNone onSome

def natZero : L :=
  lam2 "z" "s" (v "z")

def natSucc (n : L) : L :=
  lam2 "z" "s" (app (v "s") n)

def natCase (n zCase sCase : L) : L :=
  app2 n zCase sCase

def natPred : L :=
  lam "n" (natCase (v "n") natZero (lam "p" (v "p")))

def natAdd : L :=
  app .Y <|
    lam "self" <|
      lam "a" <|
        lam "b" <|
          natCase (v "a")
            (v "b")
            (lam "a1" (natSucc (app2 (v "self") (v "a1") (v "b"))))

def natEq : L :=
  app .Y <|
    lam "self" <|
      lam "a" <|
        lam "b" <|
          natCase (v "a")
            (natCase (v "b") tru (lam "b1" fls))
            (lam "a1"
              (natCase (v "b")
                fls
                (lam "b1" (app2 (v "self") (v "a1") (v "b1")))))

def natLt : L :=
  app .Y <|
    lam "self" <|
      lam "a" <|
        lam "b" <|
          natCase (v "a")
            (natCase (v "b") fls (lam "b1" tru))
            (lam "a1"
              (natCase (v "b")
                fls
                (lam "b1" (app2 (v "self") (v "a1") (v "b1")))))

/-! ## Scott constructors/case for `Expr` (Phase 8 encoding) -/

def exprBVar (n : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app (v "cBVar") n)

def exprMVar (m : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app (v "cMVar") m)

def exprSort (u : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app (v "cSort") u)

def exprConst (c us : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app2 (v "cConst") c us)

def exprApp (f a : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app2 (v "cApp") f a)

def exprLam (bn bi ty body : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app4 (v "cLam") bn bi ty body)

def exprForall (bn bi ty body : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app4 (v "cForall") bn bi ty body)

def exprLet (bn bi ty val body : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app5 (v "cLet") bn bi ty val body)

def exprLit (l : L) : L :=
  lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
    (app (v "cLit") l)

def exprCase (e cBVar cMVar cSort cConst cApp cLam cForall cLet cLit : L) : L :=
  app9 e cBVar cMVar cSort cConst cApp cLam cForall cLet cLit

/-! ## Shifting and instantiation (Phase 9 helpers encoded as λ) -/

/--
Shift de Bruijn indices:
`shiftBVarSky cutoff inc e` increments `bvar i` by `inc` when `i ≥ cutoff`.
-/
def shiftBVarSky : L :=
  app .Y <|
    lam "self" <|
      lam "cutoff" <|
        lam "inc" <|
          lam "e" <|
            exprCase (v "e")
              (lam "i"
                (app2 (app2 natLt (v "i") (v "cutoff"))
                  (exprBVar (v "i"))
                  (exprBVar (app2 natAdd (v "i") (v "inc")))))
              (lam "m" (exprMVar (v "m")))
              (lam "u" (exprSort (v "u")))
              (lam "c" (lam "us" (exprConst (v "c") (v "us"))))
              (lam "f"
                (lam "a"
                  (exprApp
                    (app3 (v "self") (v "cutoff") (v "inc") (v "f"))
                    (app3 (v "self") (v "cutoff") (v "inc") (v "a")))))
              (lam "bn"
                (lam "bi"
                  (lam "ty"
                    (lam "body"
                      (exprLam (v "bn") (v "bi")
                        (app3 (v "self") (v "cutoff") (v "inc") (v "ty"))
                        (app3 (v "self") (natSucc (v "cutoff")) (v "inc") (v "body")))))))
              (lam "bn"
                (lam "bi"
                  (lam "ty"
                    (lam "body"
                      (exprForall (v "bn") (v "bi")
                        (app3 (v "self") (v "cutoff") (v "inc") (v "ty"))
                        (app3 (v "self") (natSucc (v "cutoff")) (v "inc") (v "body")))))))
              (lam "bn"
                (lam "bi"
                  (lam "ty"
                    (lam "val"
                      (lam "body"
                        (exprLet (v "bn") (v "bi")
                          (app3 (v "self") (v "cutoff") (v "inc") (v "ty"))
                          (app3 (v "self") (v "cutoff") (v "inc") (v "val"))
                          (app3 (v "self") (natSucc (v "cutoff")) (v "inc") (v "body"))))))))
              (lam "l" (exprLit (v "l")))

/--
Instantiate the *outermost* bound variable (index `0`) with `val`.

This matches `Expr.instantiate1` specialized to its use in Phase 9 WHNF (β/ζ).
-/
def instantiate1Sky : L :=
  lam2 "val" "body" <|
    let go :=
      app .Y <|
        lam "self" <|
          lam "k" <|
            lam "e" <|
              exprCase (v "e")
                (lam "i"
                  (app2 (app2 natLt (v "i") (v "k"))
                    (exprBVar (v "i"))
                    (app2 (app2 natEq (v "i") (v "k"))
                      (app3 shiftBVarSky natZero (v "k") (v "val"))
                      (exprBVar (app natPred (v "i"))))))
                (lam "m" (exprMVar (v "m")))
                (lam "u" (exprSort (v "u")))
                (lam "c" (lam "us" (exprConst (v "c") (v "us"))))
                (lam "f"
                  (lam "a"
                    (exprApp
                      (app2 (v "self") (v "k") (v "f"))
                      (app2 (v "self") (v "k") (v "a")))))
                (lam "bn"
                  (lam "bi"
                    (lam "ty"
                      (lam "body"
                        (exprLam (v "bn") (v "bi")
                          (app2 (v "self") (v "k") (v "ty"))
                          (app2 (v "self") (natSucc (v "k")) (v "body")))))))
                (lam "bn"
                  (lam "bi"
                    (lam "ty"
                      (lam "body"
                        (exprForall (v "bn") (v "bi")
                          (app2 (v "self") (v "k") (v "ty"))
                          (app2 (v "self") (natSucc (v "k")) (v "body")))))))
                (lam "bn"
                  (lam "bi"
                    (lam "ty"
                      (lam "val"
                        (lam "body"
                          (exprLet (v "bn") (v "bi")
                            (app2 (v "self") (v "k") (v "ty"))
                            (app2 (v "self") (v "k") (v "val"))
                            (app2 (v "self") (natSucc (v "k")) (v "body"))))))))
                (lam "l" (exprLit (v "l")))
    app2 go natZero (v "body")

/-! ## WHNF as λ term (β/ζ, left spine) -/

/-- One WHNF step: `Expr → Option Expr`. -/
def whnfStepSky : L :=
  app .Y <|
    lam "self" <|
      lam "e" <|
        exprCase (v "e")
          (lam "i" optNone)
          (lam "m" optNone)
          (lam "u" optNone)
          (lam "c" (lam "us" optNone))
          (lam "f"
            (lam "a"
              (optCase (app (v "self") (v "f"))
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
                (lam "f'" (optSome (exprApp (v "f'") (v "a")))))))
          (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
          (lam "bn" (lam "bi" (lam "ty" (lam "body" optNone))))
          (lam "bn"
            (lam "bi"
              (lam "ty"
                (lam "val"
                  (lam "body" (optSome (app2 instantiate1Sky (v "val") (v "body"))))))))
          (lam "l" optNone)

/-- Bounded WHNF: iterates `whnfStepSky` up to `fuel` times. -/
def whnfSky : L :=
  app .Y
    (lam "self"
      (lam "fuel"
        (lam "e"
          (natCase (v "fuel")
            (v "e")
            (lam "n"
              (optCase (app whnfStepSky (v "e"))
                (v "e")
                (lam "e'" (app2 (v "self") (v "n") (v "e'")))))))))

/-! ## Closed compilation and a tiny execution helper -/

def compileClosed? (t : L) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) t

def whnfStepComb? : Option Comb :=
  compileClosed? whnfStepSky

def whnfComb? : Option Comb :=
  compileClosed? whnfSky

def encodeNatComb? (n : Nat) : Option Comb :=
  compileClosed? (Expr.Scott.encodeNat n)

def runWhnfTagFuel (fuelWhnf fuelReduce : Nat) (e : Expr Nat Unit Unit Unit) : Option String := do
  let whnf <- whnfComb?
  let fuelC <- encodeNatComb? fuelWhnf
  let eC <- Lean4LeanSKY.Enc.compileExprNatUnit? e
  let out := SKYExec.reduceFuel fuelReduce (Comb.app (Comb.app whnf fuelC) eC)
  Lean4LeanSKY.Decode.exprTagFuel fuelReduce out

end WHNFSKY

end LeanKernel
end LoF
end HeytingLean
