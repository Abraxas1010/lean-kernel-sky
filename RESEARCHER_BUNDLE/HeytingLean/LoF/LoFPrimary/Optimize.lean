import Mathlib.Data.List.FinRange
import HeytingLean.LoF.LoFPrimary.Syntax
import HeytingLean.LoF.LoFPrimary.Normalization
import HeytingLean.MiniC.Syntax

/-
# LoFPrimary.Optimize — small, verified simplifications + ROBDD builder

This module provides:

* `simplify` : deterministic normalization using the oriented calling/crossing/void rules.
* `ROBDD`    : a reduced ordered binary decision diagram (fixed variable order).
* `mkROBDD`  : build an ROBDD for a given `Expr n` and variable order.
* `bddToMiniCExpr` : render an ROBDD to a MiniC boolean expression (0/1 encoded).

The goal is to shrink expressions before code generation while preserving semantics.
-/

namespace HeytingLean
namespace LoF
namespace LoFPrimary
namespace Optimize

open Expr

variable {n : Nat}

/-- A deterministic, terminating simplifier for primary expressions. -/
def simplify : Expr n → Expr n
  | .void => .void
  | .var i => .var i
  | .mark A =>
      let A' := simplify A
      match A' with
      | .mark B => B                       -- crossing: mark (mark A) -> A
      | _ => .mark A'
  | .juxt A B =>
      let A' := simplify A
      let B' := simplify B
      match A', B' with
      | .void, X => X                      -- void absorption (left/right)
      | X, .void => X
      | _ , _ =>
          if _h : A' = B' then A' else .juxt A' B'   -- calling: A A -> A

private lemma eval_simplify_juxt (A' B' : Expr n) (ρ : Fin n → Bool) :
    LoFPrimary.eval
        (match A', B' with
         | .void, X => X
         | X, .void => X
         | _, _ => if A' = B' then A' else .juxt A' B') ρ
      = (LoFPrimary.eval A' ρ || LoFPrimary.eval B' ρ) := by
  cases A' with
  | void =>
      cases B' with
      | void => simp [LoFPrimary.eval]
      | var j => simp [LoFPrimary.eval]
      | mark B => simp [LoFPrimary.eval]
      | juxt B C =>
          cases hB : LoFPrimary.eval B ρ <;> cases hC : LoFPrimary.eval C ρ <;>
            simp [LoFPrimary.eval, hB, hC]
  | var i =>
      cases B' with
      | void => simp [LoFPrimary.eval]
      | var j =>
          by_cases hEq : Expr.var i = Expr.var j
          · cases hEq
            simp [LoFPrimary.eval]
          · cases hj : ρ j <;>
              simp [LoFPrimary.eval, hEq, hj]
      | mark B =>
          cases hB : LoFPrimary.eval B ρ <;>
            simp [LoFPrimary.eval, hB]
      | juxt B C =>
          cases hB : LoFPrimary.eval B ρ <;> cases hC : LoFPrimary.eval C ρ <;>
            simp [LoFPrimary.eval, hB, hC]
  | mark A1 =>
      cases B' with
      | void => simp [LoFPrimary.eval]
      | var j =>
          cases hj : ρ j <;>
            simp [LoFPrimary.eval, hj]
      | mark B1 =>
          by_cases hEq : Expr.mark A1 = Expr.mark B1
          · cases hEq
            simp [LoFPrimary.eval]
          · cases hB : LoFPrimary.eval B1 ρ <;>
              simp [LoFPrimary.eval, hEq, hB]
      | juxt B C =>
          cases hB : LoFPrimary.eval B ρ <;> cases hC : LoFPrimary.eval C ρ <;>
            simp [LoFPrimary.eval, hB, hC]
  | juxt A1 A2 =>
      cases B' with
      | void => simp [LoFPrimary.eval]
      | var j =>
          cases hj : ρ j <;>
            simp [LoFPrimary.eval, hj]
      | mark B1 =>
          cases hB : LoFPrimary.eval B1 ρ <;>
            simp [LoFPrimary.eval, hB]
      | juxt B1 B2 =>
          by_cases hEq : Expr.juxt A1 A2 = Expr.juxt B1 B2
          · cases hEq
            simp [LoFPrimary.eval]
          · cases hB1 : LoFPrimary.eval B1 ρ <;> cases hB2 : LoFPrimary.eval B2 ρ <;>
              simp [LoFPrimary.eval, hEq, hB1, hB2]

theorem eval_simplify (A : Expr n) (ρ : Fin n → Bool) :
    LoFPrimary.eval (simplify A) ρ = LoFPrimary.eval A ρ := by
  induction A generalizing ρ with
  | void => rfl
  | var i => rfl
  | mark A ih =>
      have hA' : LoFPrimary.eval A ρ = LoFPrimary.eval (simplify A) ρ := by
        simpa using (ih ρ).symm
      cases h : simplify A <;>
        simp [simplify, h, LoFPrimary.eval, hA']
  | juxt A B ihA ihB =>
      have hA' : LoFPrimary.eval (simplify A) ρ = LoFPrimary.eval A ρ := ihA ρ
      have hB' : LoFPrimary.eval (simplify B) ρ = LoFPrimary.eval B ρ := ihB ρ
      have hjuxt' :
          LoFPrimary.eval (simplify (.juxt A B)) ρ =
            (LoFPrimary.eval (simplify A) ρ || LoFPrimary.eval (simplify B) ρ) := by
        simpa [simplify] using eval_simplify_juxt (simplify A) (simplify B) ρ
      have hjuxt'' :
          LoFPrimary.eval (simplify (.juxt A B)) ρ =
            (LoFPrimary.eval A ρ || LoFPrimary.eval B ρ) := by
        simpa [hA', hB'] using hjuxt'
      simpa [LoFPrimary.eval] using hjuxt''

/-!
## Reduced Ordered BDDs

We build a canonical DAG for a fixed variable order (list of distinct `Fin n`).
We collapse identical low/high children (standard ROBDD reduction).
-/

inductive BDD (n : Nat) where
  | leaf (b : Bool)
  | node (v : Fin n) (low high : BDD n)
deriving DecidableEq, Repr

@[simp] def BDD.eval : BDD n → (Fin n → Bool) → Bool
  | .leaf b, _ => b
  | .node v l h, ρ => if ρ v then h.eval ρ else l.eval ρ

private def build (order : List (Fin n)) (f : (Fin n → Bool) → Bool) : BDD n :=
  match order with
  | [] =>
      -- No variables left: evaluate once on default valuation.
      BDD.leaf (f (fun _ => false))
  | v :: vs =>
      let f0 : (Fin n → Bool) → Bool := fun ρ => f (fun i => !decide (i = v) && ρ i)
      let f1 : (Fin n → Bool) → Bool := fun ρ => f (fun i => decide (i = v) || ρ i)
      let low := build vs f0
      let high := build vs f1
      if _h : low = high then
        low   -- reduction rule
      else
        BDD.node v low high

/-- Build a reduced ordered BDD for expression `A`, using the given variable order. -/
def mkROBDD (order : List (Fin n)) (A : Expr n) : BDD n :=
  build order (eval A)

/-- Default variable order: increasing `Fin` indices. -/
def defaultOrder (n : Nat) : List (Fin n) :=
  List.finRange n

/-!
## Render an ROBDD to MiniC boolean expressions (0/1 encoded).

We produce an expression equivalent to the BDD decision tree. This preserves sharing only
logically (the emitted expression is a tree), which is fine for the small n we target here.
-/

open HeytingLean.MiniC

private def iteBool (c t e : MiniC.Expr) : MiniC.Expr :=
  -- encode `c ? t : e` using 0/1 booleans: (c && t) || (!c && e)
  MiniC.Expr.or (MiniC.Expr.and c t) (MiniC.Expr.and (MiniC.Expr.not c) e)

def bddToMiniCExpr (nameOf : Fin n → String) : BDD n → MiniC.Expr
  | .leaf b => MiniC.Expr.boolLit b
  | .node v low high =>
      let cv := MiniC.Expr.var (nameOf v)
      iteBool cv (bddToMiniCExpr nameOf high) (bddToMiniCExpr nameOf low)

/-! ## ROBDD evaluation and correctness -/

private def restrict (order : List (Fin n)) (ρ : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ order then ρ i else false

private lemma restrict_cons (v : Fin n) (vs : List (Fin n)) (ρ : Fin n → Bool) :
    restrict (v :: vs) ρ = fun i => if i = v then ρ v else restrict vs ρ i := by
  funext i
  by_cases h : i = v
  · subst h
    simp [restrict]
  · simp [restrict, h, List.mem_cons]

private lemma build_eval (order : List (Fin n)) (f : (Fin n → Bool) → Bool) (ρ : Fin n → Bool) :
    (build order f).eval ρ = f (restrict order ρ) := by
  induction order generalizing f with
  | nil =>
      have h : restrict ([] : List (Fin n)) ρ = fun _ => false := by
        funext i
        simp [restrict]
      simp [build, h]
  | cons v vs ih =>
      -- Unfold the builder and reason by cases on the reduction branch and the input bit.
      let f0 : (Fin n → Bool) → Bool := fun ρ' => f (fun i => !decide (i = v) && ρ' i)
      let f1 : (Fin n → Bool) → Bool := fun ρ' => f (fun i => decide (i = v) || ρ' i)
      have h0 : (build vs f0).eval ρ = f0 (restrict vs ρ) := ih f0
      have h1 : (build vs f1).eval ρ = f1 (restrict vs ρ) := ih f1
      by_cases hEq : build vs f0 = build vs f1
      · have hbuild : build (v :: vs) f = build vs f0 := by
          have hEq' :
              build vs (fun ρ => f (fun i => !decide (i = v) && ρ i)) =
                build vs (fun ρ => f (fun i => decide (i = v) || ρ i)) := by
            simpa [f0, f1] using hEq
          simp [build, f0, dif_pos hEq']
        have hSame : f0 (restrict vs ρ) = f1 (restrict vs ρ) := by
          have : (build vs f0).eval ρ = (build vs f1).eval ρ := by simp [hEq]
          simpa [h0, h1] using this
        cases hv : ρ v with
        | false =>
            have hR : f (restrict (v :: vs) ρ) = f0 (restrict vs ρ) := by
              dsimp [f0]
              have hres : restrict (v :: vs) ρ = fun i => !decide (i = v) && restrict vs ρ i := by
                funext i
                by_cases hi : i = v
                · subst hi
                  simp [restrict_cons, hv]
                · simp [restrict_cons, hi]
              simp [hres]
            calc
              (build (v :: vs) f).eval ρ = (build vs f0).eval ρ := by
                simp [hbuild]
              _ = f0 (restrict vs ρ) := h0
              _ = f (restrict (v :: vs) ρ) := hR.symm
        | true =>
            have hR : f (restrict (v :: vs) ρ) = f1 (restrict vs ρ) := by
              dsimp [f1]
              have hres : restrict (v :: vs) ρ = fun i => decide (i = v) || restrict vs ρ i := by
                funext i
                by_cases hi : i = v
                · subst hi
                  simp [restrict_cons, hv]
                · simp [restrict_cons, hi]
              simp [hres]
            calc
              (build (v :: vs) f).eval ρ = (build vs f0).eval ρ := by
                simp [hbuild]
              _ = f0 (restrict vs ρ) := h0
              _ = f1 (restrict vs ρ) := hSame
              _ = f (restrict (v :: vs) ρ) := hR.symm
      · have hbuild : build (v :: vs) f = BDD.node v (build vs f0) (build vs f1) := by
          have hEq' :
              ¬build vs (fun ρ => f (fun i => !decide (i = v) && ρ i)) =
                build vs (fun ρ => f (fun i => decide (i = v) || ρ i)) := by
            simpa [f0, f1] using hEq
          simp [build, f0, f1, dif_neg hEq']
        cases hv : ρ v with
          | false =>
              have hR : f (restrict (v :: vs) ρ) = f0 (restrict vs ρ) := by
                dsimp [f0]
                have hres : restrict (v :: vs) ρ = fun i => !decide (i = v) && restrict vs ρ i := by
                  funext i
                  by_cases hi : i = v
                  · subst hi
                    simp [restrict_cons, hv]
                  · simp [restrict_cons, hi]
                simp [hres]
              calc
                (build (v :: vs) f).eval ρ =
                    (if ρ v then (build vs f1).eval ρ else (build vs f0).eval ρ) := by
                  simp [hbuild, BDD.eval]
                _ = (build vs f0).eval ρ := by simp [hv]
                _ = f0 (restrict vs ρ) := h0
                _ = f (restrict (v :: vs) ρ) := hR.symm
          | true =>
              have hR : f (restrict (v :: vs) ρ) = f1 (restrict vs ρ) := by
                dsimp [f1]
                have hres : restrict (v :: vs) ρ = fun i => decide (i = v) || restrict vs ρ i := by
                  funext i
                  by_cases hi : i = v
                  · subst hi
                    simp [restrict_cons, hv]
                  · simp [restrict_cons, hi]
                simp [hres]
              calc
                (build (v :: vs) f).eval ρ =
                    (if ρ v then (build vs f1).eval ρ else (build vs f0).eval ρ) := by
                  simp [hbuild, BDD.eval]
                _ = (build vs f1).eval ρ := by simp [hv]
                _ = f1 (restrict vs ρ) := h1
                _ = f (restrict (v :: vs) ρ) := hR.symm

lemma restrict_defaultOrder (ρ : Fin n → Bool) :
    restrict (defaultOrder n) ρ = ρ := by
  funext i
  simp [restrict, defaultOrder, List.mem_finRange]

theorem mkROBDD_eval_default (A : Expr n) (ρ : Fin n → Bool) :
    (mkROBDD (defaultOrder n) A).eval ρ = LoFPrimary.eval A ρ := by
  simpa [mkROBDD, restrict_defaultOrder] using
    (build_eval (order := defaultOrder n) (f := LoFPrimary.eval A) (ρ := ρ))

theorem mkROBDD_eq_iff (A B : Expr n) :
    LoFPrimary.Eqv (n := n) A B ↔
      mkROBDD (defaultOrder n) A = mkROBDD (defaultOrder n) B := by
  constructor
  · intro h
    have hfun : (LoFPrimary.eval A) = (LoFPrimary.eval B) := funext h
    simp [mkROBDD, hfun]
  · intro h ρ
    have h' := congrArg (fun bdd => BDD.eval bdd ρ) h
    simpa [mkROBDD_eval_default] using h'

/-! ## Composite: LoFPrimary → MiniC using the optimizer. -/

def toMiniCExpr (nameOf : Fin n → String) (A : Expr n) : MiniC.Expr :=
  let A' := simplify A
  let bdd := mkROBDD (defaultOrder n) A'
  bddToMiniCExpr nameOf bdd

end Optimize
end LoFPrimary
end LoF
end HeytingLean
