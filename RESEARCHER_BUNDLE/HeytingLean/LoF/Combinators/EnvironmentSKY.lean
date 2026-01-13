import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.WHNFSKY

/-!
# LeanKernel.EnvironmentSKY (Phase 21)

Computation-plane encoding for a minimal constant environment:

* encode a list of constant declarations as Scott data accessible from SKY,
* provide linear lookup by name,
* expose `constType?` / `constValue?` as closed λ terms compilable to `Comb`,
* provide fuel-bounded runners that decode only constructor tags (sanity / cross-validation).

This phase deliberately ignores universe instantiation (δ unfolding will thread universes later).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

namespace EnvironmentSKY

open Expr

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

/-! ## Constant declarations and environments as Scott data -/

/-- A 3-field record encoding: `ConstDecl = (name, type, value?)`. -/
def constDeclEncode (name ty val? : L) : L :=
  lam "c" (app3 (v "c") name ty val?)

def envEmpty : L :=
  listNil

def envExtend (env decl : L) : L :=
  listCons decl env

/-! ## Lookup and projections (as closed λ terms) -/

def envLookup? : L :=
  app .Y <|
    lam "self" <|
      lam "env" <|
        lam "name" <|
          listCase (v "env")
            optNone
            (lam "decl" <|
              lam "rest" <|
                app (v "decl") <|
                  lam "declName" <|
                    lam "declTy" <|
                      lam "declVal" <|
                        app2 (app2 natEq (v "declName") (v "name"))
                          (optSome (v "decl"))
                          (app2 (v "self") (v "rest") (v "name")))

def constType? : L :=
  lam2 "env" "name" <|
    optCase (app2 envLookup? (v "env") (v "name"))
      optNone
      (lam "decl" <|
        app (v "decl") <|
          lam "n" <| lam "ty" <| lam "val" <|
            optSome (v "ty"))

def constValue? : L :=
  lam2 "env" "name" <|
    optCase (app2 envLookup? (v "env") (v "name"))
      optNone
      (lam "decl" <|
        app (v "decl") <|
          lam "n" <| lam "ty" <| lam "val" <|
            (v "val"))

/-! ## Encoding concrete `Environment.Env` instances (data-only) -/

namespace Enc

def unit : Unit → L := fun _ => .K
def nat : Nat → L := Expr.Scott.encodeNat
def string : String → L := fun _ => .K

def expr : Expr Nat Unit Unit Unit → L :=
  Expr.Scott.encode nat unit unit unit string

def optExpr : Option (Expr Nat Unit Unit Unit) → L
  | none => optNone
  | some e => optSome (expr e)

def constDecl
    (us : List (ULevel Unit Unit))
    (d : Environment.ConstDecl Nat Unit Unit Unit) : L :=
  let name := nat d.name
  let ty := expr (d.type us)
  let val? :=
    match d.value? with
    | none => optNone
    | some f => optSome (expr (f us))
  constDeclEncode name ty val?

def env (us : List (ULevel Unit Unit)) (e : Environment.Env Nat Unit Unit Unit) : L :=
  let rec go : List (Environment.ConstDecl Nat Unit Unit Unit) → L
    | [] => envEmpty
    | d :: ds => envExtend (go ds) (constDecl us d)
  go e.consts

end Enc

def envEncode (us : List (ULevel Unit Unit)) (e : Environment.Env Nat Unit Unit Unit) : L :=
  Enc.env us e

def envComb? (us : List (ULevel Unit Unit)) (e : Environment.Env Nat Unit Unit Unit) : Option Comb :=
  Bracket.Lam.compileClosed? (envEncode us e)

def compileNat? (n : Nat) : Option Comb :=
  Bracket.Lam.compileClosed? (Enc.nat n)

def envLookupComb? : Option Comb :=
  Bracket.Lam.compileClosed? envLookup?

def constTypeComb? : Option Comb :=
  Bracket.Lam.compileClosed? constType?

def constValueComb? : Option Comb :=
  Bracket.Lam.compileClosed? constValue?

def optExprToExprOrKComb? : Option Comb :=
  /- `none ↦ K`, `some x ↦ x` -/
  Bracket.Lam.compileClosed? (lam "o" (optCase (v "o") (.K) (lam "x" (v "x"))))

def decodeOptExprTagFuel (fuel : Nat) (o : Comb) : Option (Option String) :=
  match optExprToExprOrKComb? with
  | none => none
  | some optExprToExprOrK =>
      let out := SKYExec.reduceFuel fuel (Comb.app optExprToExprOrK o)
      if out = Comb.K then
        some none
      else
        (Lean4LeanSKY.Decode.exprTagFuel fuel out).map some

def runConstTypeTagFuel (fuel : Nat) (us : List (ULevel Unit Unit))
    (e : Environment.Env Nat Unit Unit Unit) (c : Nat) : Option (Option String) := do
  let envC <- envComb? us e
  let nameC <- compileNat? c
  let f <- constTypeComb?
  let out := SKYExec.reduceFuel fuel (Comb.app (Comb.app f envC) nameC)
  decodeOptExprTagFuel fuel out

def runConstValueTagFuel (fuel : Nat) (us : List (ULevel Unit Unit))
    (e : Environment.Env Nat Unit Unit Unit) (c : Nat) : Option (Option String) := do
  let envC <- envComb? us e
  let nameC <- compileNat? c
  let f <- constValueComb?
  let out := SKYExec.reduceFuel fuel (Comb.app (Comb.app f envC) nameC)
  decodeOptExprTagFuel fuel out

end EnvironmentSKY

end LeanKernel
end LoF
end HeytingLean
