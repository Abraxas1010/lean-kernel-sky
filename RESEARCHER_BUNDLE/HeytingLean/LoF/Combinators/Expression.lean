import HeytingLean.LoF.LeanKernel.UniverseLevel

/-!
# LeanKernel.Expression (Phase 8)

Project-local expression AST intended to mirror Lean's (and Lean4Lean's) core
kernel-level expression shapes, while remaining lightweight enough to Scott-encode
into SKY via bracket abstraction in later phases.

This Phase 8 deliverable provides:
- `BinderInfo` and `Literal` (minimal kernel-facing payloads),
- `Expr` with a *9-way* constructor split,
- a Scott encoding hook `Expr.Scott.encode` into `Bracket.Lam` (parameterized by encoders).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

/-- Minimal binder info flags (modeled on Lean's `BinderInfo`). -/
inductive BinderInfo where
  | default
  | implicit
  | strictImplicit
  | instImplicit
deriving Repr, DecidableEq

/-- Minimal literal payload (modeled on Lean's `Literal`). -/
inductive Literal where
  | natVal (n : Nat)
  | strVal (s : String)
deriving Repr, DecidableEq

/-- Kernel expression AST with a deliberately small 9-way constructor split.

We parameterize universe levels separately from expression metavariables:
- `Param` / `MetaLevel` appear inside `ULevel` values (Phase 7),
- `MetaExpr` is used for expression metavariables.

The chosen 9 constructors align with the “core” shapes used by kernels:
`bvar`, `mvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE`, `lit`.
-/
inductive Expr (Name Param MetaLevel MetaExpr : Type u) where
  | bvar : Nat → Expr Name Param MetaLevel MetaExpr
  | mvar : MetaExpr → Expr Name Param MetaLevel MetaExpr
  | sort : ULevel Param MetaLevel → Expr Name Param MetaLevel MetaExpr
  | const : Name → List (ULevel Param MetaLevel) → Expr Name Param MetaLevel MetaExpr
  | app : Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr → Expr Name Param MetaLevel MetaExpr
  | lam :
      (binderName : Name) →
      (binderInfo : BinderInfo) →
      (binderType : Expr Name Param MetaLevel MetaExpr) →
      (body : Expr Name Param MetaLevel MetaExpr) →
      Expr Name Param MetaLevel MetaExpr
  | forallE :
      (binderName : Name) →
      (binderInfo : BinderInfo) →
      (binderType : Expr Name Param MetaLevel MetaExpr) →
      (body : Expr Name Param MetaLevel MetaExpr) →
      Expr Name Param MetaLevel MetaExpr
  | letE :
      (binderName : Name) →
      (binderInfo : BinderInfo) →
      (type : Expr Name Param MetaLevel MetaExpr) →
      (value : Expr Name Param MetaLevel MetaExpr) →
      (body : Expr Name Param MetaLevel MetaExpr) →
      Expr Name Param MetaLevel MetaExpr
  | lit : Literal → Expr Name Param MetaLevel MetaExpr
deriving Repr, DecidableEq

namespace Expr

variable {Name Param MetaLevel MetaExpr : Type u}

/-- Map all payload types in an expression. -/
def map {Name' Param' MetaLevel' MetaExpr' : Type u}
    (fName : Name → Name')
    (fParam : Param → Param')
    (fMetaLevel : MetaLevel → MetaLevel')
    (fMetaExpr : MetaExpr → MetaExpr') :
    Expr Name Param MetaLevel MetaExpr → Expr Name' Param' MetaLevel' MetaExpr'
  | .bvar n => .bvar n
  | .mvar m => .mvar (fMetaExpr m)
  | .sort u => .sort (ULevel.map fParam fMetaLevel u)
  | .const c us => .const (fName c) (us.map (ULevel.map fParam fMetaLevel))
  | .app f a => .app (map fName fParam fMetaLevel fMetaExpr f) (map fName fParam fMetaLevel fMetaExpr a)
  | .lam bn bi ty body =>
      .lam (fName bn) bi
        (map fName fParam fMetaLevel fMetaExpr ty)
        (map fName fParam fMetaLevel fMetaExpr body)
  | .forallE bn bi ty body =>
      .forallE (fName bn) bi
        (map fName fParam fMetaLevel fMetaExpr ty)
        (map fName fParam fMetaLevel fMetaExpr body)
  | .letE bn bi ty val body =>
      .letE (fName bn) bi
        (map fName fParam fMetaLevel fMetaExpr ty)
        (map fName fParam fMetaLevel fMetaExpr val)
        (map fName fParam fMetaLevel fMetaExpr body)
  | .lit l => .lit l

/-- A small structural size metric (useful later for bounded compilation). -/
def size : Expr Name Param MetaLevel MetaExpr → Nat
  | .bvar _ => 1
  | .mvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f a => size f + size a + 1
  | .lam _ _ ty body => size ty + size body + 1
  | .forallE _ _ ty body => size ty + size body + 1
  | .letE _ _ ty val body => size ty + size val + size body + 1
  | .lit _ => 1

/-! ## Scott encoding into SKY (via untyped λ + bracket abstraction) -/

namespace Scott

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
def lam4 (a b c d : String) (body : L) : L := lam a (lam b (lam c (lam d body)))
def lam9 (a b c d e f g h i : String) (body : L) : L :=
  lam a (lam b (lam c (lam d (lam e (lam f (lam g (lam h (lam i body))))))))

end L

open L

def encodeNat : Nat → L
  | 0 => lam2 "z" "s" (v "z")
  | Nat.succ n => lam2 "z" "s" (L.app (v "s") (encodeNat n))

def encodeList (enc : α → L) : List α → L
  | [] => lam2 "n" "c" (v "n")
  | x :: xs => lam2 "n" "c" (app2 (v "c") (enc x) (encodeList enc xs))

def encodeBinderInfo : BinderInfo → L
  | .default => lam4 "cDefault" "cImplicit" "cStrict" "cInst" (v "cDefault")
  | .implicit => lam4 "cDefault" "cImplicit" "cStrict" "cInst" (v "cImplicit")
  | .strictImplicit => lam4 "cDefault" "cImplicit" "cStrict" "cInst" (v "cStrict")
  | .instImplicit => lam4 "cDefault" "cImplicit" "cStrict" "cInst" (v "cInst")

def encodeLiteral (encString : String → L) : Literal → L
  | .natVal n => lam2 "cNat" "cStr" (L.app (v "cNat") (encodeNat n))
  | .strVal s => lam2 "cNat" "cStr" (L.app (v "cStr") (encString s))

/-- Scott encoding for expressions (parameterized by encodings of payload types).

Constructor order (as binder arguments):
`cBVar cMVar cSort cConst cApp cLam cForall cLet cLit`.
-/
def encode
    (encName : Name → L)
    (encParam : Param → L)
    (encMetaLevel : MetaLevel → L)
    (encMetaExpr : MetaExpr → L)
    (encString : String → L) :
    Expr Name Param MetaLevel MetaExpr → L
  | .bvar n =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (L.app (v "cBVar") (encodeNat n))
  | .mvar m =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (L.app (v "cMVar") (encMetaExpr m))
  | .sort u =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (L.app (v "cSort") (ULevel.Scott.encode encParam encMetaLevel u))
  | .const c us =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (app2 (v "cConst") (encName c) (encodeList (ULevel.Scott.encode encParam encMetaLevel) us))
  | .app f a =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (app2 (v "cApp")
          (encode encName encParam encMetaLevel encMetaExpr encString f)
          (encode encName encParam encMetaLevel encMetaExpr encString a))
  | .lam bn bi ty body =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (app4 (v "cLam")
          (encName bn)
          (encodeBinderInfo bi)
          (encode encName encParam encMetaLevel encMetaExpr encString ty)
          (encode encName encParam encMetaLevel encMetaExpr encString body))
  | .forallE bn bi ty body =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (app4 (v "cForall")
          (encName bn)
          (encodeBinderInfo bi)
          (encode encName encParam encMetaLevel encMetaExpr encString ty)
          (encode encName encParam encMetaLevel encMetaExpr encString body))
  | .letE bn bi ty val body =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (app5 (v "cLet")
          (encName bn)
          (encodeBinderInfo bi)
          (encode encName encParam encMetaLevel encMetaExpr encString ty)
          (encode encName encParam encMetaLevel encMetaExpr encString val)
          (encode encName encParam encMetaLevel encMetaExpr encString body))
  | .lit l =>
      lam9 "cBVar" "cMVar" "cSort" "cConst" "cApp" "cLam" "cForall" "cLet" "cLit"
        (L.app (v "cLit") (encodeLiteral encString l))

/-- Compile a Scott-encoded expression to a closed SKY term (when payload encodings are closed). -/
def compileClosed?
    (encName : Name → L)
    (encParam : Param → L)
    (encMetaLevel : MetaLevel → L)
    (encMetaExpr : MetaExpr → L)
    (encString : String → L)
    (e : Expr Name Param MetaLevel MetaExpr) :
    Option HeytingLean.LoF.Comb :=
  Bracket.Lam.compileClosed? (Var := String) (encode encName encParam encMetaLevel encMetaExpr encString e)

end Scott

end Expr

end LeanKernel
end LoF
end HeytingLean
