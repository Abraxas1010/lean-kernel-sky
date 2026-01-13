import HeytingLean.LoF.Combinators.BracketAbstraction

/-!
# LeanKernel.UniverseLevel (Phase 7)

This module introduces a small, project-local universe level AST intended to
mirror Lean's (and Lean4Lean's) level expressions, while remaining lightweight
enough to Scott-encode into SKY via bracket abstraction in later phases.

We keep the AST *parameterized* over:
- `Param`: universe parameters (typically `Name` or de Bruijn indices)
- `Meta`: metavariables used by definitional equality / unification

The initial deliverable is:
- the AST `ULevel Param Meta`,
- a simple numeric semantics `eval` under valuations,
- a Scott encoding into `Bracket.Lam` (parameterized by encoders for `Param`/`Meta`).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Bracket

/-- Universe level expressions (Lean-style). -/
inductive ULevel (Param Meta : Type u) where
  | zero : ULevel Param Meta
  | succ : ULevel Param Meta → ULevel Param Meta
  | max : ULevel Param Meta → ULevel Param Meta → ULevel Param Meta
  | imax : ULevel Param Meta → ULevel Param Meta → ULevel Param Meta
  | param : Param → ULevel Param Meta
  | mvar : Meta → ULevel Param Meta
deriving Repr, DecidableEq

namespace ULevel

variable {Param Meta : Type u}

/-- Map the parameter and metavariable payloads. -/
def map {Param' Meta' : Type u} (f : Param → Param') (g : Meta → Meta') :
    ULevel Param Meta → ULevel Param' Meta'
  | .zero => .zero
  | .succ u => .succ (map f g u)
  | .max a b => .max (map f g a) (map f g b)
  | .imax a b => .imax (map f g a) (map f g b)
  | .param p => .param (f p)
  | .mvar m => .mvar (g m)

/-- Numeric semantics of universe levels under valuations.

This uses the standard interpretation of `imax` used by Lean:
`imax u v` evaluates to `0` when `v` evaluates to `0`, and otherwise to `max u v`.
-/
def eval (ρParam : Param → Nat) (ρMeta : Meta → Nat) : ULevel Param Meta → Nat
  | .zero => 0
  | .succ u => Nat.succ (eval ρParam ρMeta u)
  | .max a b => Nat.max (eval ρParam ρMeta a) (eval ρParam ρMeta b)
  | .imax a b =>
      let vb := eval ρParam ρMeta b
      if vb = 0 then 0 else Nat.max (eval ρParam ρMeta a) vb
  | .param p => ρParam p
  | .mvar m => ρMeta m

@[simp] theorem eval_zero (ρParam : Param → Nat) (ρMeta : Meta → Nat) :
    eval ρParam ρMeta (.zero : ULevel Param Meta) = 0 := rfl

@[simp] theorem eval_succ (ρParam : Param → Nat) (ρMeta : Meta → Nat) (u : ULevel Param Meta) :
    eval ρParam ρMeta (.succ u) = Nat.succ (eval ρParam ρMeta u) := rfl

@[simp] theorem eval_max (ρParam : Param → Nat) (ρMeta : Meta → Nat) (a b : ULevel Param Meta) :
    eval ρParam ρMeta (.max a b) = Nat.max (eval ρParam ρMeta a) (eval ρParam ρMeta b) := rfl

theorem eval_imax (ρParam : Param → Nat) (ρMeta : Meta → Nat) (a b : ULevel Param Meta) :
    eval ρParam ρMeta (.imax a b) =
      (let vb := eval ρParam ρMeta b
       if vb = 0 then 0 else Nat.max (eval ρParam ρMeta a) vb) := rfl

@[simp] theorem eval_param (ρParam : Param → Nat) (ρMeta : Meta → Nat) (p : Param) :
    eval ρParam ρMeta (.param p : ULevel Param Meta) = ρParam p := rfl

@[simp] theorem eval_mvar (ρParam : Param → Nat) (ρMeta : Meta → Nat) (m : Meta) :
    eval ρParam ρMeta (.mvar m : ULevel Param Meta) = ρMeta m := rfl

/-! ## Scott encoding into SKY (via untyped λ + bracket abstraction) -/

namespace Scott

abbrev L : Type := Bracket.Lam String

namespace L

def v (s : String) : L := Bracket.Lam.var s
def app (f a : L) : L := Bracket.Lam.app f a
def lam (x : String) (body : L) : L := Bracket.Lam.lam x body

def app2 (f a b : L) : L := app (app f a) b
def lam2 (x y : String) (body : L) : L := lam x (lam y body)

def lam6 (a b c d e f : String) (body : L) : L :=
  lam a (lam b (lam c (lam d (lam e (lam f body)))))

end L

open L

/-- Scott encoding for universe levels (parameterized by encodings of payload types).

Constructor order (as binder arguments):
`cZero cSucc cMax cIMax cParam cMVar`.
-/
def encode (encParam : Param → L) (encMeta : Meta → L) : ULevel Param Meta → L
  | .zero =>
      lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar" (v "cZero")
  | .succ u =>
      lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar"
        (app (v "cSucc") (encode encParam encMeta u))
  | .max a b =>
      lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar"
        (app2 (v "cMax") (encode encParam encMeta a) (encode encParam encMeta b))
  | .imax a b =>
      lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar"
        (app2 (v "cIMax") (encode encParam encMeta a) (encode encParam encMeta b))
  | .param p =>
      lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar"
        (app (v "cParam") (encParam p))
  | .mvar m =>
      lam6 "cZero" "cSucc" "cMax" "cIMax" "cParam" "cMVar"
        (app (v "cMVar") (encMeta m))

/-- Compile a Scott-encoded universe level to a closed SKY term (when payload encodings are closed). -/
def compileClosed? (encParam : Param → L) (encMeta : Meta → L) (u : ULevel Param Meta) :
    Option HeytingLean.LoF.Comb :=
  Bracket.Lam.compileClosed? (Var := String) (encode encParam encMeta u)

end Scott

end ULevel

end LeanKernel
end LoF
end HeytingLean
