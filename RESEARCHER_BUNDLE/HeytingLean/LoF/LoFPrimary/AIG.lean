import HeytingLean.LoF.LoFPrimary.MuxNet
import Std.Sat.AIG.If
import Std.Sat.AIG.Lemmas
import Std.Sat.AIG.RefVec

/-!
# LoFPrimary.AIG

An AND-inverter graph (AIG) compilation target for the LoF kernel.

* Representation + semantics are provided by Lean's verified `Std.Sat.AIG`.
* Compilation target is `MuxNet.Net n` (ITE/MUX syntax tree).
* MUX nodes compile using `Std.Sat.AIG.mkIfCached`.
* AIGER ASCII (`.aag`) emission is provided for the demo CLI.

This module is intentionally combinational single-output (AIGER `L = 0`, `O = 1`).
-/

namespace HeytingLean
namespace LoF
namespace LoFPrimary
namespace AIG

open MuxNet

/-- A compiled AIG (single-output, combinational). -/
structure Graph (n : Nat) where
  aig : Std.Sat.AIG (Fin n)
  output : aig.Ref

/-- Evaluate a compiled AIG using `Std.Sat.AIG.denote`. -/
def Graph.eval {n : Nat} (g : Graph n) (ρ : Fin n → Bool) : Bool :=
  Std.Sat.AIG.denote ρ ⟨g.aig, g.output⟩

/-! ## Prefix utilities -/

private theorem IsPrefix.trans {α : Type}
    {decls1 decls2 decls3 : Array (Std.Sat.AIG.Decl α)}
    (h12 : Std.Sat.AIG.IsPrefix decls1 decls2) (h23 : Std.Sat.AIG.IsPrefix decls2 decls3) :
    Std.Sat.AIG.IsPrefix decls1 decls3 := by
  refine Std.Sat.AIG.IsPrefix.of (Nat.le_trans h12.size_le h23.size_le) ?_
  intro idx hidx
  have := h23.idx_eq idx (by
    have := h12.size_le
    omega)
  simpa [h12.idx_eq idx hidx] using this

/-! ## Compilation state -/

/-- Compilation state: the current AIG together with stable references to each primary input. -/
structure CState (n : Nat) where
  aig : Std.Sat.AIG (Fin n)
  inputs : aig.RefVec n

/-- A compilation result: updated state plus an output reference in the updated AIG. -/
structure CResult (n : Nat) where
  state : CState n
  out : state.aig.Ref

/-- Constant reference (AIG index `0` is `.false`; `invert=true` gives constant `true`). -/
def constRef {α : Type} [Hashable α] [DecidableEq α] (aig : Std.Sat.AIG α) (b : Bool) : aig.Ref :=
  ⟨0, b, aig.hzero⟩

/-! ## Seeding primary inputs -/

private theorem RefVec.get_irrel {α : Type} [Hashable α] [DecidableEq α] {aig : Std.Sat.AIG α}
    (s : aig.RefVec len) (idx : Nat) (h1 h2 : idx < len) : s.get idx h1 = s.get idx h2 := by
  cases s with
  | mk refs hrefs =>
    simp [Std.Sat.AIG.RefVec.get]

/-- Seed an empty AIG with *all* inputs `0..n-1` (as atoms), producing an input `RefVec`. -/
def seedInputs (n : Nat) : CState n :=
  let aig0 := Std.Sat.AIG.empty (α := Fin n)
  go 0 (by simp) aig0 (Std.Sat.AIG.RefVec.empty (aig := aig0))
where
  go (i : Nat) (hi : i ≤ n) (aig : Std.Sat.AIG (Fin n)) (vec : aig.RefVec i) : CState n :=
    if h : i < n then
      let v : Fin n := ⟨i, h⟩
      let res := aig.mkAtom v
      let hcast : aig.decls.size ≤ res.aig.decls.size :=
        Std.Sat.AIG.LawfulOperator.le_size (f := Std.Sat.AIG.mkAtom) (aig := aig) v
      let vec' := (vec.cast hcast).push res.ref
      go (i + 1) (Nat.succ_le_of_lt h) res.aig vec'
    else
      have hi' : i = n := Nat.le_antisymm hi (Nat.le_of_not_lt h)
      { aig := aig, inputs := by simpa [hi'] using vec }
termination_by n - i

private def InputsOK {n : Nat} (s : CState n) (ρ : Fin n → Bool) : Prop :=
  ∀ v : Fin n, Std.Sat.AIG.denote ρ ⟨s.aig, s.inputs.get v.val v.isLt⟩ = ρ v

private theorem seedInputs_ok {n : Nat} (ρ : Fin n → Bool) : InputsOK (seedInputs n) ρ := by
  classical
  let rec go_ok (i : Nat) (hi : i ≤ n) (aig : Std.Sat.AIG (Fin n)) (vec : aig.RefVec i)
      (hok : ∀ (j : Nat) (hj : j < i),
        Std.Sat.AIG.denote ρ ⟨aig, vec.get j hj⟩ = ρ ⟨j, lt_of_lt_of_le hj hi⟩) :
      InputsOK (seedInputs.go n i hi aig vec) ρ := by
    by_cases h : i < n
    · have hi' : i + 1 ≤ n := Nat.succ_le_of_lt h
      let v : Fin n := ⟨i, h⟩
      let res := aig.mkAtom v
      let hcast : aig.decls.size ≤ res.aig.decls.size :=
        Std.Sat.AIG.LawfulOperator.le_size (f := Std.Sat.AIG.mkAtom) (aig := aig) v
      let vec' := (vec.cast hcast).push res.ref
      have hok' :
          ∀ (j : Nat) (hj : j < i + 1),
            Std.Sat.AIG.denote ρ ⟨res.aig, vec'.get j hj⟩ = ρ ⟨j, lt_of_lt_of_le hj hi'⟩ := by
        intro j hj
        by_cases hjEq : j = i
        · subst j
          have hget : vec'.get i hj = res.ref := by
            have h0 : vec'.get i hj = vec'.get i (by omega) :=
              RefVec.get_irrel (s := vec') (idx := i) _ _
            have h1 : vec'.get i (by omega) = res.ref := by
              simp [vec']
            exact h0.trans h1
          have hden : Std.Sat.AIG.denote ρ ⟨res.aig, res.ref⟩ = ρ v := by
            simp [res]
          simpa [hget, v] using hden
        · have hjlt : j < i := by omega
          have hprefix : Std.Sat.AIG.IsPrefix aig.decls res.aig.decls :=
            Std.Sat.AIG.LawfulOperator.isPrefix_aig (f := Std.Sat.AIG.mkAtom) (aig := aig) v
          have hden_cast :
              Std.Sat.AIG.denote ρ ⟨res.aig, (vec.get j hjlt).cast hcast⟩
                =
              Std.Sat.AIG.denote ρ ⟨aig, vec.get j hjlt⟩ := by
            simpa using
              (Std.Sat.AIG.denote.eq_of_isPrefix (entry := ⟨aig, vec.get j hjlt⟩)
                (newAIG := res.aig) (hprefix := hprefix) (assign := ρ))
          have hget : vec'.get j hj = (vec.get j hjlt).cast hcast := by
            have h0 : vec'.get j hj = vec'.get j (by omega) :=
              RefVec.get_irrel (s := vec') (idx := j) _ _
            have h1 : vec'.get j (by omega) = (vec.cast hcast).get j hjlt := by
              simpa [vec'] using
                (Std.Sat.AIG.RefVec.get_push_ref_lt (s := vec.cast hcast) (ref := res.ref)
                  (idx := j) (hidx := hjlt))
            have h2 : (vec.cast hcast).get j hjlt = (vec.get j hjlt).cast hcast := by
              simp
            exact h0.trans (h1.trans h2)
          have := hok j hjlt
          simpa [hget] using (hden_cast.trans this)
      have ih : InputsOK (seedInputs.go n (i + 1) hi' res.aig vec') ρ :=
        go_ok (i := i + 1) (hi := hi') (aig := res.aig) (vec := vec') hok'
      -- unfold the outer `if` in `seedInputs.go` once
      rw [seedInputs.go.eq_1]
      simp [h]
      exact ih
    · have hi' : i = n := Nat.le_antisymm hi (Nat.le_of_not_lt h)
      subst hi'
      rw [seedInputs.go.eq_1]
      simp
      intro v
      have := hok v.val (by exact v.isLt)
      simpa using this
  unfold seedInputs
  simp
  exact
    go_ok (i := 0) (hi := by simp) (aig := Std.Sat.AIG.empty (α := Fin n)) (vec := Std.Sat.AIG.RefVec.empty)
      (by intro j hj; cases hj)

/-! ## Compilation -/

private abbrev CompileOut {n : Nat} (s : CState n) : Type :=
  { r : CResult n // Std.Sat.AIG.IsPrefix s.aig.decls r.state.aig.decls }

/-- Compile a `MuxNet.Net n` into a `Std.Sat.AIG` ref, returning an explicit prefix proof. -/
def compileAux {n : Nat} (net : Net n) (s : CState n) : CompileOut s :=
  match net with
  | .const b =>
      ⟨⟨s, constRef s.aig b⟩, Std.Sat.AIG.IsPrefix.rfl⟩
  | .mux v lo hi =>
      let rLo := compileAux lo s
      let s1 := rLo.1.state
      let rHi := compileAux hi s1
      let s2 := rHi.1.state
      let loRef : s2.aig.Ref := rLo.1.out.cast rHi.2.size_le
      let selRef : s2.aig.Ref := s2.inputs.get v.val v.isLt
      let input : s2.aig.TernaryInput := ⟨selRef, rHi.1.out, loRef⟩
      let res := s2.aig.mkIfCached input
      let hprefixIf : Std.Sat.AIG.IsPrefix s2.aig.decls res.aig.decls :=
        Std.Sat.AIG.LawfulOperator.isPrefix_aig (f := Std.Sat.AIG.mkIfCached) (aig := s2.aig) input
      let s3 : CState n := { aig := res.aig, inputs := s2.inputs.cast hprefixIf.size_le }
      let hprefix : Std.Sat.AIG.IsPrefix s.aig.decls s3.aig.decls :=
        IsPrefix.trans (IsPrefix.trans rLo.2 rHi.2) hprefixIf
      ⟨⟨s3, res.ref⟩, hprefix⟩

/-- Compile a `MuxNet.Net n` to an AIG graph (seed inputs first). -/
def ofMuxNet {n : Nat} (net : Net n) : Graph n :=
  let s0 := seedInputs n
  let r := (compileAux net s0).1
  { aig := r.state.aig, output := r.out }

/-! ## Correctness -/

private theorem InputsOK_of_prefix
    {n : Nat} {s : CState n} {ρ : Fin n → Bool} {aig' : Std.Sat.AIG (Fin n)}
    (hprefix : Std.Sat.AIG.IsPrefix s.aig.decls aig'.decls) (hok : InputsOK s ρ) :
    InputsOK { aig := aig', inputs := s.inputs.cast hprefix.size_le } ρ := by
  intro v
  have hden :
      Std.Sat.AIG.denote ρ ⟨aig', (s.inputs.get v.val v.isLt).cast hprefix.size_le⟩
        =
      Std.Sat.AIG.denote ρ ⟨s.aig, s.inputs.get v.val v.isLt⟩ := by
    simpa using
      (Std.Sat.AIG.denote.eq_of_isPrefix (entry := ⟨s.aig, s.inputs.get v.val v.isLt⟩)
        (newAIG := aig') (hprefix := hprefix) (assign := ρ))
  simpa using (hden.trans (hok v))

theorem compileAux_correct
    {n : Nat} (net : Net n) (s : CState n) (ρ : Fin n → Bool) (hok : InputsOK s ρ) :
    let r := (compileAux net s).1
    InputsOK r.state ρ ∧ Std.Sat.AIG.denote ρ ⟨r.state.aig, r.out⟩ = MuxNet.eval net ρ := by
  induction net generalizing s with
  | const b =>
      refine ⟨?_, ?_⟩
      · simpa [compileAux] using hok
      · have h0 : s.aig.decls[0]'s.aig.hzero = Std.Sat.AIG.Decl.false := s.aig.hconst
        have hden :
            Std.Sat.AIG.denote ρ ⟨s.aig, ⟨0, b, s.aig.hzero⟩⟩ = b := by
          simpa using
            (Std.Sat.AIG.denote_idx_false (aig := s.aig) (assign := ρ)
              (start := 0) (invert := b) (hstart := s.aig.hzero) h0)
        simpa [compileAux, constRef, MuxNet.eval] using hden
  | mux v lo hi ihLo ihHi =>
      let rLo := compileAux lo s
      let s1 := rLo.1.state
      have hlo := ihLo (s := s) hok
      have hok1 : InputsOK s1 ρ := by
        simpa [s1, rLo] using hlo.1
      have hloEval : Std.Sat.AIG.denote ρ ⟨s1.aig, rLo.1.out⟩ = MuxNet.eval lo ρ := by
        simpa [s1, rLo] using hlo.2
      let rHi := compileAux hi s1
      let s2 := rHi.1.state
      have hhi := ihHi (s := s1) hok1
      have hok2 : InputsOK s2 ρ := by
        simpa [s2, rHi] using hhi.1
      have hhiEval : Std.Sat.AIG.denote ρ ⟨s2.aig, rHi.1.out⟩ = MuxNet.eval hi ρ := by
        simpa [s2, rHi] using hhi.2
      have hlo_cast :
          Std.Sat.AIG.denote ρ ⟨s2.aig, rLo.1.out.cast rHi.2.size_le⟩
            =
          Std.Sat.AIG.denote ρ ⟨s1.aig, rLo.1.out⟩ := by
        simpa using
          (Std.Sat.AIG.denote.eq_of_isPrefix (entry := ⟨s1.aig, rLo.1.out⟩) (newAIG := s2.aig)
            (hprefix := rHi.2) (assign := ρ))
      let loRef : s2.aig.Ref := rLo.1.out.cast rHi.2.size_le
      let selRef : s2.aig.Ref := s2.inputs.get v.val v.isLt
      let input : s2.aig.TernaryInput := ⟨selRef, rHi.1.out, loRef⟩
      let res := s2.aig.mkIfCached input
      have hprefixIf : Std.Sat.AIG.IsPrefix s2.aig.decls res.aig.decls :=
        Std.Sat.AIG.LawfulOperator.isPrefix_aig (f := Std.Sat.AIG.mkIfCached) (aig := s2.aig) input
      have hokOut :
          InputsOK { aig := res.aig, inputs := s2.inputs.cast hprefixIf.size_le } ρ :=
        InputsOK_of_prefix (s := s2) (ρ := ρ) (hprefix := hprefixIf) hok2
      refine ⟨hokOut, ?_⟩
      have hsel : Std.Sat.AIG.denote ρ ⟨s2.aig, selRef⟩ = ρ v := hok2 v
      have hloEval' : Std.Sat.AIG.denote ρ ⟨s2.aig, loRef⟩ = MuxNet.eval lo ρ := by
        simpa [loRef] using (hlo_cast.trans hloEval)
      have hif :
          Std.Sat.AIG.denote ρ res
            =
          if Std.Sat.AIG.denote ρ ⟨s2.aig, selRef⟩ then
              Std.Sat.AIG.denote ρ ⟨s2.aig, rHi.1.out⟩
            else
              Std.Sat.AIG.denote ρ ⟨s2.aig, loRef⟩ := by
        simp [res, input]
      calc
        Std.Sat.AIG.denote ρ ⟨res.aig, res.ref⟩ = Std.Sat.AIG.denote ρ res := by rfl
        _ = if Std.Sat.AIG.denote ρ ⟨s2.aig, selRef⟩ then
              Std.Sat.AIG.denote ρ ⟨s2.aig, rHi.1.out⟩
            else
              Std.Sat.AIG.denote ρ ⟨s2.aig, loRef⟩ := hif
        _ = if ρ v then MuxNet.eval hi ρ else MuxNet.eval lo ρ := by
              cases hv : ρ v <;> simp [hsel, hhiEval, hloEval', hv]

theorem ofMuxNet_correct {n : Nat} (net : Net n) (ρ : Fin n → Bool) :
    (ofMuxNet net).eval ρ = MuxNet.eval net ρ := by
  unfold ofMuxNet Graph.eval
  let s0 := seedInputs n
  have hok0 : InputsOK s0 ρ := seedInputs_ok (n := n) (ρ := ρ)
  have h := compileAux_correct (net := net) (s := s0) (ρ := ρ) hok0
  simpa using h.2

/-- End-to-end: `LoFPrimary.Expr n → AIG` correctness. -/
theorem loFToAIG_correct {n : Nat} (A : Expr n) (ρ : Fin n → Bool) :
    (ofMuxNet (MuxNet.toMuxNet (n := n) A)).eval ρ = LoFPrimary.eval A ρ := by
  simpa [MuxNet.eval_toMuxNet] using ofMuxNet_correct (net := MuxNet.toMuxNet (n := n) A) (ρ := ρ)

/-! ## AIGER ASCII emission -/

private def refLit {n : Nat} {aig : Std.Sat.AIG (Fin n)} (r : aig.Ref) : Nat :=
  2 * r.gate + (if r.invert then 1 else 0)

private def isGate {α : Type} : Std.Sat.AIG.Decl α → Bool
  | .gate .. => true
  | _ => false

private def countAnds {α : Type} (decls : Array (Std.Sat.AIG.Decl α)) : Nat :=
  (decls.toList.filter isGate).length

/-- Emit ASCII AIGER (`.aag`) for a single-output graph. -/
def Graph.toAigerAscii {n : Nat} (g : Graph n) : String :=
  let decls := g.aig.decls
  let maxVar := decls.size - 1
  let numAnds := countAnds decls
  let header := s!"aag {maxVar} {n} 0 1 {numAnds}"
  let inputs := (List.range n).map (fun i => toString (2 * (i + 1)))
  let output := toString (refLit g.output)
  let andLines :=
    (List.range decls.size).filterMap (fun idx =>
      match decls[idx]? with
      | some (Std.Sat.AIG.Decl.gate l r) => some s!"{2 * idx} {l.val} {r.val}"
      | _ => none)
  String.intercalate "\n" (header :: inputs ++ [output] ++ andLines)

end AIG
end LoFPrimary
end LoF
end HeytingLean
