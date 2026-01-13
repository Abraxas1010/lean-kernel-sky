import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.STLC

/-!
# STLCSKY — a tiny STLC checker compiled to SKY (Phase 4a)

We encode STLC syntax (types/terms/contexts) using Scott encodings in an untyped
lambda syntax, compile it to SKY combinators via bracket abstraction, and run it
using the fuel-limited reducer from `SKYExec`.

This module is intentionally small and demo-oriented: the primary consumer is the
`lof_stlc_demo` executable.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Bracket

namespace STLCSKY

abbrev L : Type := Bracket.Lam String

namespace L

def v (s : String) : L := Bracket.Lam.var s
def app (f a : L) : L := Bracket.Lam.app f a
def lam (x : String) (body : L) : L := Bracket.Lam.lam x body

def app2 (f a b : L) : L := app (app f a) b
def app3 (f a b c : L) : L := app (app2 f a b) c
def app4 (f a b c d : L) : L := app (app3 f a b c) d
def app5 (f a b c d e : L) : L := app (app4 f a b c d) e

def lam2 (x y : String) (body : L) : L := lam x (lam y body)
def lam3 (x y z : String) (body : L) : L := lam x (lam y (lam z body))
def lam4 (x y z w : String) (body : L) : L := lam x (lam y (lam z (lam w body)))
def lam5 (x y z w u : String) (body : L) : L := lam x (lam y (lam z (lam w (lam u body))))

end L

open L

/-! ## Core encodings (Scott/Church) -/

def I : L :=
  app2 (.S) (.K) (.K)

def tru : L := .K
def fls : L := app (.K) I

def boolAnd : L :=
  lam2 "p" "q" (app2 (v "p") (v "q") fls)

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

def listNil : L :=
  lam2 "n" "c" (v "n")

def listCons (hd tl : L) : L :=
  lam2 "n" "c" (app2 (v "c") hd tl)

def listCase (xs onNil onCons : L) : L :=
  app2 xs onNil onCons

def tyBool : L :=
  lam2 "b" "a" (v "b")

def tyArr (a b : L) : L :=
  lam2 "b" "a" (app2 (v "a") a b)

def tyCase (t onBool onArr : L) : L :=
  app2 t onBool onArr

def termVar (n : L) : L :=
  lam5 "cVar" "cApp" "cLam" "cTrue" "cFalse" (app (v "cVar") n)

def termApp (f a : L) : L :=
  lam5 "cVar" "cApp" "cLam" "cTrue" "cFalse" (app2 (v "cApp") f a)

def termLam (tArg body : L) : L :=
  lam5 "cVar" "cApp" "cLam" "cTrue" "cFalse" (app2 (v "cLam") tArg body)

def termTrue : L :=
  lam5 "cVar" "cApp" "cLam" "cTrue" "cFalse" (v "cTrue")

def termFalse : L :=
  lam5 "cVar" "cApp" "cLam" "cTrue" "cFalse" (v "cFalse")

def termCase (t cVar cApp cLam cTrue cFalse : L) : L :=
  app5 t cVar cApp cLam cTrue cFalse

/-! ## Recursive functions in SKY (via primitive `Y`) -/

def lookupTy : L :=
  app .Y
    (lam "self"
      (lam "ctx"
        (lam "n"
          (natCase (v "n")
            (listCase (v "ctx") optNone (lam "h" (lam "t" (optSome (v "h")))))
            (lam "n1"
              (listCase (v "ctx") optNone (lam "h" (lam "t" (app2 (v "self") (v "t") (v "n1"))))))))))

def eqTy : L :=
  app .Y
    (lam "self"
      (lam "t"
        (lam "u"
          (tyCase (v "t")
            (tyCase (v "u") tru (lam "u1" (lam "u2" fls)))
            (lam "t1"
              (lam "t2"
                (tyCase (v "u")
                  fls
                  (lam "u1"
                    (lam "u2"
                      (app2 boolAnd
                        (app2 (v "self") (v "t1") (v "u1"))
                        (app2 (v "self") (v "t2") (v "u2"))))))))))))

def infer : L :=
  app .Y
    (lam "self"
      (lam "ctx"
        (lam "tm"
          (let caseVar : L :=
              lam "n" (app2 lookupTy (v "ctx") (v "n"));
            let caseApp : L :=
              lam "f"
                (lam "a"
                  (optCase (app2 (v "self") (v "ctx") (v "f"))
                    optNone
                    (lam "tf"
                      (tyCase (v "tf")
                        optNone
                        (lam "tArg"
                          (lam "tRes"
                            (optCase (app2 (v "self") (v "ctx") (v "a"))
                              optNone
                              (lam "ta"
                                (app2 (app2 eqTy (v "ta") (v "tArg")) (optSome (v "tRes")) optNone)))))))));
            let caseLam : L :=
              lam "tArg"
                (lam "body"
                  (optCase (app2 (v "self") (listCons (v "tArg") (v "ctx")) (v "body"))
                    optNone
                    (lam "tBody" (optSome (tyArr (v "tArg") (v "tBody"))))));
            termCase (v "tm") caseVar caseApp caseLam (optSome tyBool) (optSome tyBool)))))

def check : L :=
  lam "ctx"
    (lam "tm"
      (lam "ty"
        (optCase (app2 infer (v "ctx") (v "tm"))
          fls
          (lam "tInf" (app2 eqTy (v "tInf") (v "ty"))))))

/-! ## Encoding STLC data as closed `Lam` terms -/

def encodeNat : Nat → L
  | 0 => natZero
  | Nat.succ n => natSucc (encodeNat n)

def encodeTy : STLC.Ty → L
  | .bool => tyBool
  | .arrow a b => tyArr (encodeTy a) (encodeTy b)

def encodeCtx : STLC.Ctx → L
  | [] => listNil
  | t :: ts => listCons (encodeTy t) (encodeCtx ts)

def encodeTerm : STLC.Term → L
  | .var i => termVar (encodeNat i)
  | .app f a => termApp (encodeTerm f) (encodeTerm a)
  | .lam tArg body => termLam (encodeTy tArg) (encodeTerm body)
  | .ttrue => termTrue
  | .tfalse => termFalse

def compileClosed? (t : L) : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) t

def checkComb? : Option Comb :=
  compileClosed? check

def runCheckFuel (fuel : Nat) (Γ : STLC.Ctx) (t : STLC.Term) (ty : STLC.Ty) : Option Bool := do
  let chk <- checkComb?
  let Γc <- compileClosed? (encodeCtx Γ)
  let tc <- compileClosed? (encodeTerm t)
  let tyc <- compileClosed? (encodeTy ty)
  let out := SKYExec.reduceFuel fuel (Comb.app (Comb.app (Comb.app chk Γc) tc) tyc)
  SKYExec.decodeChurchBoolFuel fuel out

end STLCSKY

end Combinators
end LoF
end HeytingLean
