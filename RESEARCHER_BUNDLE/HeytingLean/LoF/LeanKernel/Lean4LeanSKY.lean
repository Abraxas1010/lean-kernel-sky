import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.LeanKernel.UniverseLevel
import HeytingLean.LoF.LeanKernel.Expression

/-!
# LeanKernel.Lean4LeanSKY (Phase 14)

Executable compilation utilities that turn staged kernel *data* into SKY (`Comb`)
via the Scott encodings (Phases 7–8) and bracket abstraction (Phase 2).

This phase is intentionally focused on the **data plane**:
- compile `ULevel` and `Expr` into SKY terms,
- provide small fuel-bounded decoders for constructor tags (sanity),
- provide a bounded heap+stack “machine image” generator for later FPGA demos.

The next incremental step (later phases) is to Scott-encode *kernel algorithms*
(WHNF/DefEq/Infer) and compile those computations to SKY as well.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LoF
open HeytingLean.LoF.Combinators

namespace Lean4LeanSKY

open Expr
open HeytingLean.LoF.Combinators.SKYExec
open HeytingLean.LoF.Combinators.SKYMachineBounded

/-! ## Tiny combinator utilities -/

def appN : Comb → List Comb → Comb :=
  fun f args => args.foldl (fun acc a => Comb.app acc a) f

def constFn (arity : Nat) (tag : Comb) : Comb :=
  Nat.rec (motive := fun _ => Comb) tag (fun _ acc => Comb.app Comb.K acc) arity

/-! ## Closed encoders for common payload instantiations -/

abbrev L : Type := HeytingLean.LoF.Combinators.Bracket.Lam String

namespace Enc

def unit : Unit → L := fun _ => .K
def nat : Nat → L := Expr.Scott.encodeNat
def string : String → L := fun _ => .K

def compileULevelNatUnit? (u : ULevel Unit Unit) : Option Comb :=
  ULevel.Scott.compileClosed? (Param := Unit) (Meta := Unit) unit unit u

def compileExprNatUnit? (e : Expr Nat Unit Unit Unit) : Option Comb :=
  Expr.Scott.compileClosed?
    (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit)
    nat unit unit unit string e

end Enc

/-! ## Decoding tags of Scott-encoded data inside SKY -/

namespace Decode

/-! ### Shared tag decoders -/

def ulevelDecodeTerm (u : Comb) : Comb :=
  /-
  Scott encoding for `ULevel` (Phase 7) has 6 cases with these payload arities:
  - `zero` : 0
  - `succ` : 1
  - `max`  : 2
  - `imax` : 2
  - `param`: 1
  - `mvar` : 1
  -/
  let tagZero := Comb.K
  let tagSucc := Comb.S
  let tagMax := Comb.Y
  -- Tags must be *normal forms* under SKY reduction (avoid `Y`-headed applications).
  let tagIMax := Comb.app Comb.K Comb.K
  let tagParam := Comb.app Comb.K Comb.S
  let tagMVar := Comb.app Comb.K Comb.Y
  appN u
    [ constFn 0 tagZero
    , constFn 1 tagSucc
    , constFn 2 tagMax
    , constFn 2 tagIMax
    , constFn 1 tagParam
    , constFn 1 tagMVar ]

def ulevelTagTermFuel (fuel : Nat) (u : Comb) : Comb :=
  SKYExec.reduceFuel fuel (ulevelDecodeTerm u)

/-!
Decode to a human-readable constructor tag string by reducing (fuel-bounded).
-/
def ulevelTagFuel (fuel : Nat) (u : Comb) : Option String :=
  let tagZero := Comb.K
  let tagSucc := Comb.S
  let tagMax := Comb.Y
  let tagIMax := Comb.app Comb.K Comb.K
  let tagParam := Comb.app Comb.K Comb.S
  let tagMVar := Comb.app Comb.K Comb.Y
  let out := ulevelTagTermFuel fuel u
  if out = tagZero then
    some "zero"
  else if out = tagSucc then
    some "succ"
  else if out = tagMax then
    some "max"
  else if out = tagIMax then
    some "imax"
  else if out = tagParam then
    some "param"
  else if out = tagMVar then
    some "mvar"
  else
    none

def exprDecodeTerm (e : Comb) : Comb :=
  /-
  Scott encoding for `Expr` (Phase 8) has 9 cases with these payload arities:
  - `bvar`   : 1
  - `mvar`   : 1
  - `sort`   : 1
  - `const`  : 2
  - `app`    : 2
  - `lam`    : 4
  - `forallE`: 4
  - `letE`   : 5
  - `lit`    : 1
  -/
  let tagBVar := Comb.K
  let tagMVar := Comb.S
  let tagSort := Comb.Y
  -- Tags must be *normal forms* under SKY reduction (avoid `Y`-headed applications).
  let tagConst := Comb.app Comb.K Comb.K
  let tagApp := Comb.app Comb.K Comb.S
  let tagLam := Comb.app Comb.K Comb.Y
  let tagForall := Comb.app Comb.S Comb.K
  let tagLet := Comb.app Comb.S Comb.S
  let tagLit := Comb.app Comb.S Comb.Y
  appN e
    [ constFn 1 tagBVar
    , constFn 1 tagMVar
    , constFn 1 tagSort
    , constFn 2 tagConst
    , constFn 2 tagApp
    , constFn 4 tagLam
    , constFn 4 tagForall
    , constFn 5 tagLet
    , constFn 1 tagLit ]

def exprTagTermFuel (fuel : Nat) (e : Comb) : Comb :=
  SKYExec.reduceFuel fuel (exprDecodeTerm e)

/-!
Decode to a human-readable constructor tag string by reducing (fuel-bounded).
-/
def exprTagFuel (fuel : Nat) (e : Comb) : Option String :=
  let tagBVar := Comb.K
  let tagMVar := Comb.S
  let tagSort := Comb.Y
  let tagConst := Comb.app Comb.K Comb.K
  let tagApp := Comb.app Comb.K Comb.S
  let tagLam := Comb.app Comb.K Comb.Y
  let tagForall := Comb.app Comb.S Comb.K
  let tagLet := Comb.app Comb.S Comb.S
  let tagLit := Comb.app Comb.S Comb.Y
  let out := exprTagTermFuel fuel e
  if out = tagBVar then
    some "bvar"
  else if out = tagMVar then
    some "mvar"
  else if out = tagSort then
    some "sort"
  else if out = tagConst then
    some "const"
  else if out = tagApp then
    some "app"
  else if out = tagLam then
    some "lam"
  else if out = tagForall then
    some "forallE"
  else if out = tagLet then
    some "letE"
  else if out = tagLit then
    some "lit"
  else
    none

end Decode

/-! ## Bounded machine images (for later FPGA demos) -/

namespace Machine

def compileCombToState? (maxNodes : Nat) (t : Comb) : Option (SKYMachineBounded.State Unit) :=
  SKYMachineBounded.State.compileComb? (OracleRef := Unit) maxNodes t

def compileExprToState? (maxNodes : Nat) (e : Expr Nat Unit Unit Unit) : Option (SKYMachineBounded.State Unit) := do
  let t <- Enc.compileExprNatUnit? e
  compileCombToState? maxNodes t

def compileULevelToState? (maxNodes : Nat) (u : ULevel Unit Unit) : Option (SKYMachineBounded.State Unit) := do
  let t <- Enc.compileULevelNatUnit? u
  compileCombToState? maxNodes t

end Machine

end Lean4LeanSKY

end LeanKernel
end LoF
end HeytingLean
