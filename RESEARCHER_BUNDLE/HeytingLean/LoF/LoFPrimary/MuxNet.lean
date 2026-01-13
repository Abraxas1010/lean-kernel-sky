import HeytingLean.LoF.LoFPrimary.Optimize
import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace LoF
namespace LoFPrimary

/-!
# LoFPrimary.MuxNet

A small “bridge layer” for the semantic chain

`LoFPrimary.Expr n` → *(Boolean function)* → `Optimize.BDD n` → *(MUX/ITE network)*.

For v0 we model a MUX network as an ITE syntax tree (`Net`), and compile from
`Optimize.BDD`.  This keeps the correctness proof compositional:

`Net.eval (ofBDD (mkROBDD …)) = LoFPrimary.eval …`.
-/

namespace MuxNet

variable {n : Nat}

/-- MUX/ITE networks over variables `Fin n`. -/
inductive Net (n : Nat) where
  | const (b : Bool)
  | mux (v : Fin n) (lo hi : Net n)
deriving Repr, DecidableEq

/-- Truth-functional semantics of a MUX network. -/
@[simp] def eval : Net n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .mux v lo hi, ρ => if ρ v then eval hi ρ else eval lo ρ

/-- Compile an `Optimize.BDD` into a MUX network (node-for-node). -/
def ofBDD : LoFPrimary.Optimize.BDD n → Net n
  | .leaf b => .const b
  | .node v lo hi => .mux v (ofBDD lo) (ofBDD hi)

theorem eval_ofBDD (b : LoFPrimary.Optimize.BDD n) (ρ : Fin n → Bool) :
    eval (ofBDD b) ρ = b.eval ρ := by
  induction b with
  | leaf b => rfl
  | node v lo hi ihLo ihHi =>
      simp [ofBDD, eval, ihLo, ihHi, LoFPrimary.Optimize.BDD.eval]

theorem eval_mkROBDD_default (A : Expr n) (ρ : Fin n → Bool) :
    eval (ofBDD (LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n) A)) ρ =
      LoFPrimary.eval A ρ := by
  have h1 :=
    eval_ofBDD (b := LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n) A) (ρ := ρ)
  have h2 := LoFPrimary.Optimize.mkROBDD_eval_default (A := A) (ρ := ρ)
  exact h1.trans h2

theorem eval_mkROBDD_simplify_default (A : Expr n) (ρ : Fin n → Bool) :
    eval
        (ofBDD
          (LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n)
            (LoFPrimary.Optimize.simplify A))) ρ =
      LoFPrimary.eval A ρ := by
  have h := eval_mkROBDD_default (A := LoFPrimary.Optimize.simplify A) (ρ := ρ)
  exact h.trans (LoFPrimary.Optimize.eval_simplify (A := A) (ρ := ρ))

/-- LoFPrimary optimizer + ROBDD builder + MUX network bridge (default order). -/
def toMuxNet (A : Expr n) : Net n :=
  ofBDD (LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n) (LoFPrimary.Optimize.simplify A))

theorem eval_toMuxNet (A : Expr n) (ρ : Fin n → Bool) :
    eval (toMuxNet (n := n) A) ρ = LoFPrimary.eval A ρ := by
  simpa [toMuxNet] using eval_mkROBDD_simplify_default (A := A) (ρ := ρ)

/-- Convert a MuxNet to a MiniC expression (0/1 boolean encoding). -/
def toMiniCExpr (nameOf : Fin n → String) : Net n → MiniC.Expr
  | .const true  => MiniC.Expr.boolLit true
  | .const false => MiniC.Expr.boolLit false
  | .mux v lo hi =>
      -- ITE(v, hi, lo) = (v && hi) || (!v && lo)
      let cv := MiniC.Expr.var (nameOf v)
      MiniC.Expr.or
        (MiniC.Expr.and cv (toMiniCExpr nameOf hi))
        (MiniC.Expr.and (MiniC.Expr.not cv) (toMiniCExpr nameOf lo))

/-- A MiniC store `σ` corresponds to a boolean environment `ρ` when
    `σ(nameOf v) ≠ 0 ↔ ρ v = true` for all `v`. -/
def StoreCorresponds (nameOf : Fin n → String) (σ : MiniC.TotalStore) (ρ : Fin n → Bool) : Prop :=
  ∀ v : Fin n, (σ (nameOf v) ≠ 0) ↔ (ρ v = true)

theorem eval_toMiniCExpr (nameOf : Fin n → String) (net : Net n)
    (σ : MiniC.TotalStore) (ρ : Fin n → Bool)
    (hCorr : StoreCorresponds (n := n) nameOf σ ρ) :
    (MiniC.Expr.eval (toMiniCExpr (n := n) nameOf net) σ ≠ 0) ↔ (eval net ρ = true) := by
  induction net with
  | const b =>
      cases b <;> simp [toMiniCExpr, MiniC.Expr.eval, eval]
  | mux v lo hi ihLo ihHi =>
      have hv : (σ (nameOf v) ≠ 0) ↔ (ρ v = true) := hCorr v
      cases hρ : ρ v <;>
        simp [toMiniCExpr, MiniC.Expr.eval, eval, hρ, ihLo, ihHi, hv] at *

theorem eval_loFToMiniC (nameOf : Fin n → String) (A : Expr n)
    (σ : MiniC.TotalStore) (ρ : Fin n → Bool)
    (hCorr : StoreCorresponds (n := n) nameOf σ ρ) :
    (MiniC.Expr.eval (toMiniCExpr (n := n) nameOf (toMuxNet (n := n) A)) σ ≠ 0) ↔
      (LoFPrimary.eval A ρ = true) := by
  have h1 := eval_toMiniCExpr (n := n) nameOf (toMuxNet (n := n) A) σ ρ hCorr
  have h2 := eval_toMuxNet (n := n) (A := A) (ρ := ρ)
  simpa [h2] using h1

end MuxNet
end LoFPrimary
end LoF
end HeytingLean
