import HeytingLean.LoF.LoFPrimary.MuxNet

namespace HeytingLean
namespace LoF
namespace LoFPrimary

/-!
# LoFPrimary.GateSpec

Gate-level representation for MUX networks (`MuxNet.Net`) and a verified compiler
from `MuxNet.Net n` to a gate netlist.

For v0, the gate basis is **MUX + constants + inputs**; each `MuxNet.mux` node
becomes a single `Gate.mux`.
-/

namespace GateSpec

variable {n : Nat}

/-- Wire identifiers in a gate netlist. -/
abbrev WireId := Nat

/-- Gate types for combinational logic. -/
inductive Gate where
  | const (out : WireId) (b : Bool)           -- constant 0 or 1
  | input (out : WireId) (v : Nat)            -- primary input (variable index)
  | not   (out : WireId) (a : WireId)         -- NOT gate
  | and2  (out : WireId) (a b : WireId)       -- 2-input AND
  | or2   (out : WireId) (a b : WireId)       -- 2-input OR
  | mux   (out : WireId) (sel a b : WireId)   -- MUX: sel ? b : a
deriving Repr, DecidableEq

/-- A gate-level netlist is a list of gates plus an output wire. -/
structure Netlist where
  gates : List Gate
  output : WireId
deriving Repr

/-- Wire valuation (partial, since not all wires may be defined). -/
abbrev WireEnv := WireId → Option Bool

/-- Output wire of a gate. -/
def Gate.out : Gate → WireId
  | .const out _ => out
  | .input out _ => out
  | .not out _ => out
  | .and2 out _ _ => out
  | .or2 out _ _ => out
  | .mux out _ _ _ => out

/-- Evaluate a single gate given current wire values and primary inputs. -/
def Gate.eval (inputs : Nat → Bool) (g : Gate) (env : WireEnv) : WireEnv := fun w =>
  match g with
  | .const out b =>
      if w = out then some b else env w
  | .input out v =>
      if w = out then some (inputs v) else env w
  | .not out a =>
      if w = out then (env a).map (!·) else env w
  | .and2 out a b =>
      if w = out then do
        let va ← env a
        let vb ← env b
        return va && vb
      else env w
  | .or2 out a b =>
      if w = out then do
        let va ← env a
        let vb ← env b
        return va || vb
      else env w
  | .mux out sel a b =>
      if w = out then do
        let vs ← env sel
        let va ← env a
        let vb ← env b
        return if vs then vb else va
      else env w

/-- Evaluate a list of gates in order. -/
def evalGates (inputs : Nat → Bool) : List Gate → WireEnv → WireEnv
  | [], env => env
  | g :: gs, env => evalGates inputs gs (g.eval inputs env)

/-- `evalGates` distributes over list append. -/
theorem evalGates_append (inputs : Nat → Bool) :
    ∀ (gs₁ gs₂ : List Gate) (env : WireEnv),
      evalGates inputs (gs₁ ++ gs₂) env = evalGates inputs gs₂ (evalGates inputs gs₁ env)
  | [], gs₂, env => rfl
  | g :: gs₁, gs₂, env => by
      simp [evalGates, evalGates_append inputs gs₁ gs₂ (g.eval inputs env)]

/-- Evaluate a netlist given primary input values. -/
def Netlist.eval (nl : Netlist) (inputs : Nat → Bool) : Option Bool :=
  let finalEnv := evalGates inputs nl.gates (fun _ => none)
  finalEnv nl.output

private theorem Gate.eval_of_ne_out (inputs : Nat → Bool) (g : Gate) (env : WireEnv)
    {w : WireId} (hw : w ≠ g.out) :
    g.eval inputs env w = env w := by
  cases g with
  | const out b =>
      have hw' : w ≠ out := by simpa [Gate.out] using hw
      simp [Gate.eval, hw']
  | input out v =>
      have hw' : w ≠ out := by simpa [Gate.out] using hw
      simp [Gate.eval, hw']
  | not out a =>
      have hw' : w ≠ out := by simpa [Gate.out] using hw
      simp [Gate.eval, hw']
  | and2 out a b =>
      have hw' : w ≠ out := by simpa [Gate.out] using hw
      simp [Gate.eval, hw']
  | or2 out a b =>
      have hw' : w ≠ out := by simpa [Gate.out] using hw
      simp [Gate.eval, hw']
  | mux out sel a b =>
      have hw' : w ≠ out := by simpa [Gate.out] using hw
      simp [Gate.eval, hw']

private theorem evalGates_preserve (inputs : Nat → Bool) :
    ∀ (gs : List Gate) (env : WireEnv) (w : WireId),
      (∀ g ∈ gs, g.out ≠ w) →
      evalGates inputs gs env w = env w
  | [], env, w, _ => rfl
  | g :: gs, env, w, h => by
      have hwg : g.out ≠ w := h g (by simp)
      have hgs : ∀ g' ∈ gs, g'.out ≠ w := by
        intro g' hg'
        exact h g' (by simp [hg'])
      have hwg' : w ≠ g.out := by simpa [eq_comm] using hwg
      have hg_eval : g.eval inputs env w = env w := Gate.eval_of_ne_out (inputs := inputs) (g := g) (env := env) hwg'
      simp [evalGates, hg_eval, evalGates_preserve inputs gs (g.eval inputs env) w hgs]

private theorem evalGates_preserve_lt (inputs : Nat → Bool) (gs : List Gate) (env : WireEnv)
    (k w : WireId) (hw : w < k) (hge : ∀ g ∈ gs, k ≤ g.out) :
    evalGates inputs gs env w = env w := by
  apply evalGates_preserve (inputs := inputs) (gs := gs) (env := env) (w := w)
  intro g hg
  have hk : k ≤ g.out := hge g hg
  have : w < g.out := lt_of_lt_of_le hw hk
  exact ne_of_gt this

/-! ## Compilation: MuxNet → Netlist -/

/-- State for netlist compilation (next wire ID, accumulated gates). -/
structure CompileState (n : Nat) where
  nextWire : WireId
  gates : List Gate
  inputWires : Fin n → WireId  -- maps variables to their input wires

/-- Input-gate prefix for `n` variables, using wires `0,1,...,n-1`. -/
private def mkInputGates : Nat → List Gate
  | 0 => []
  | n + 1 => mkInputGates n ++ [Gate.input n n]

/-- Create initial state with input wires for all variables. -/
def initCompileState (n : Nat) : CompileState n :=
  { nextWire := n
    gates := mkInputGates n
    inputWires := fun v => v.val }

/-- Pure compilation of a `MuxNet.Net n`, allocating fresh wires from `k` upward.
Returns `(outWire, nextWire, newGates)`. -/
private def compilePure {n : Nat} (inputWires : Fin n → WireId) :
    MuxNet.Net n → WireId → (WireId × WireId × List Gate)
  | .const b, k => (k, k + 1, [Gate.const k b])
  | .mux v lo hi, k =>
      let (loOut, k₁, gLo) := compilePure inputWires lo k
      let (hiOut, k₂, gHi) := compilePure inputWires hi k₁
      let out := k₂
      (out, out + 1, gLo ++ gHi ++ [Gate.mux out (inputWires v) loOut hiOut])

/-- Compile a `MuxNet.Net n`, appending gates to the current state. -/
def compileMuxNet {n : Nat} (net : MuxNet.Net n) : StateM (CompileState n) WireId :=
  fun s =>
    let (outWire, nextWire, newGates) := compilePure s.inputWires net s.nextWire
    (outWire, { s with nextWire := nextWire, gates := s.gates ++ newGates })

/-- Compile a MuxNet to a complete netlist (including input gates). -/
def toNetlist {n : Nat} (net : MuxNet.Net n) : Netlist :=
  let (outWire, s') := compileMuxNet net (initCompileState n)
  { gates := s'.gates, output := outWire }

private theorem compilePure_next_eq_out_succ {n : Nat} (inputWires : Fin n → WireId)
    (net : MuxNet.Net n) (k : WireId) :
    (compilePure inputWires net k).2.1 = (compilePure inputWires net k).1 + 1 := by
  induction net generalizing k with
  | const b => simp [compilePure]
  | mux v lo hi ihLo ihHi =>
      simp [compilePure, ihLo, ihHi]

private theorem compilePure_out_ge_start {n : Nat} (inputWires : Fin n → WireId)
    (net : MuxNet.Net n) (k : WireId) :
    k ≤ (compilePure inputWires net k).1 := by
  induction net generalizing k with
  | const b => simp [compilePure]
  | mux v lo hi ihLo ihHi =>
      -- out is the `k₂` returned by compiling `hi`
      rcases hLo : compilePure inputWires lo k with ⟨loOut, k₁, gLo⟩
      have hk₁ : k ≤ k₁ := by
        have hloOut : k ≤ loOut := by
          simpa [hLo] using (ihLo (k := k))
        -- k₁ = loOut + 1
        have hk₁' : k₁ = loOut + 1 := by
          simpa [hLo] using (compilePure_next_eq_out_succ (inputWires := inputWires) (net := lo) (k := k))
        simpa [hk₁'] using Nat.le_trans hloOut (Nat.le_succ loOut)
      rcases hHi : compilePure inputWires hi k₁ with ⟨hiOut, k₂, gHi⟩
      have h_hiOut : k₁ ≤ hiOut := by
        simpa [hHi] using (ihHi (k := k₁))
      have hk₂' : k₂ = hiOut + 1 := by
        simpa [hHi] using
          (compilePure_next_eq_out_succ (inputWires := inputWires) (net := hi) (k := k₁))
      have hk₂ : k ≤ k₂ := by
        -- k ≤ k₁ ≤ hiOut ≤ hiOut+1 = k₂
        have : k ≤ hiOut := Nat.le_trans hk₁ h_hiOut
        simpa [hk₂'] using Nat.le_trans this (Nat.le_succ hiOut)
      simpa [compilePure, hLo, hHi] using hk₂

private theorem compilePure_outs_ge_start {n : Nat} (inputWires : Fin n → WireId)
    (net : MuxNet.Net n) (k : WireId) :
    ∀ g ∈ (compilePure inputWires net k).2.2, k ≤ g.out := by
  induction net generalizing k with
  | const b =>
      intro g hg
      simp [compilePure] at hg
      rcases hg with rfl
      simp [Gate.out]
  | mux v lo hi ihLo ihHi =>
      rcases hLo : compilePure inputWires lo k with ⟨loOut, k₁, gLo⟩
      have hk₁ : k ≤ k₁ := by
        have hloOut : k ≤ loOut := by
          simpa [hLo] using (compilePure_out_ge_start (inputWires := inputWires) (net := lo) (k := k))
        have hk₁' : k₁ = loOut + 1 := by
          simpa [hLo] using
            (compilePure_next_eq_out_succ (inputWires := inputWires) (net := lo) (k := k))
        simpa [hk₁'] using Nat.le_trans hloOut (Nat.le_succ loOut)
      rcases hHi : compilePure inputWires hi k₁ with ⟨hiOut, k₂, gHi⟩
      intro g hg
      -- membership splits across `gLo ++ gHi ++ [Gate.mux ...]`
      simp [compilePure, hLo, hHi] at hg
      rcases hg with hg | hg
      ·
          have hg' : g ∈ (compilePure inputWires lo k).2.2 := by
            simpa [hLo] using hg
          exact ihLo (k := k) g hg'
      · rcases hg with hg | hg
        · have : k₁ ≤ g.out := by
            -- rewrite membership back into the `compilePure` output for `hi`
            have hg' : g ∈ (compilePure inputWires hi k₁).2.2 := by simpa [hHi] using hg
            exact ihHi (k := k₁) g hg'
          exact Nat.le_trans hk₁ this
        · rcases hg with rfl
          -- the mux gate's output is `k₂`
          have h_hiOut : k₁ ≤ hiOut := by
            simpa [hHi] using
              (compilePure_out_ge_start (inputWires := inputWires) (net := hi) (k := k₁))
          have hk₂' : k₂ = hiOut + 1 := by
            simpa [hHi] using
              (compilePure_next_eq_out_succ (inputWires := inputWires) (net := hi) (k := k₁))
          have hk₂ : k ≤ k₂ := by
            have : k ≤ hiOut := Nat.le_trans hk₁ h_hiOut
            simpa [hk₂'] using Nat.le_trans this (Nat.le_succ hiOut)
          simpa [Gate.out] using hk₂

/-!
The correctness proof below is specialized to the compiler-produced netlists,
which use input wires `0,1,...,n-1` (so inputs are defined before being read).
-/

private def inputsOf {n : Nat} (ρ : Fin n → Bool) : Nat → Bool :=
  fun i => if h : i < n then ρ ⟨i, h⟩ else false

private theorem evalGates_mkInputGates {n : Nat} (inputs : Nat → Bool) (i : Nat) (hi : i < n) :
    evalGates inputs (mkInputGates n) (fun _ => none) i = some (inputs i) := by
  induction n generalizing i with
  | zero => cases (Nat.not_lt_zero _ hi)
  | succ n ih =>
      have hn : mkInputGates (n + 1) = mkInputGates n ++ [Gate.input n n] := by rfl
      have hi' : i < n ∨ i = n := Nat.lt_succ_iff_lt_or_eq.mp hi
      cases hi' with
      | inl hlt =>
          have hi_ne : i ≠ n := Nat.ne_of_lt hlt
          have hi_ne' : i ≠ (Gate.input n n).out := by
            simpa [Gate.out] using hi_ne
          -- split the append and note the final gate doesn't change wire `i`
          have := ih (i := i) hlt
          simp [hn, evalGates_append, evalGates, Gate.eval_of_ne_out (inputs := inputs)
            (g := Gate.input n n) (env := evalGates inputs (mkInputGates n) (fun _ => none)) hi_ne'] at *
          exact this
      | inr heq =>
          subst heq
          -- evaluate at `i = n` (the last gate sets wire `n`)
          simp [hn, evalGates_append, evalGates, Gate.eval]

private theorem eval_compilePure {n : Nat} (inputWires : Fin n → WireId)
    (inputs : Nat → Bool) (net : MuxNet.Net n) (ρ : Fin n → Bool) :
    ∀ (k : WireId) (env0 : WireEnv),
      (∀ v : Fin n, env0 (inputWires v) = some (ρ v)) →
      (∀ v : Fin n, inputWires v < k) →
      let (outWire, _, newGates) := compilePure inputWires net k
      (evalGates inputs newGates env0) outWire = some (MuxNet.eval net ρ)
  := by
  intro k env0 hEnv hIW
  induction net generalizing k env0 with
  | const b =>
      simp [compilePure, evalGates, Gate.eval, MuxNet.eval]
  | mux v lo hi ihLo ihHi =>
      rcases hLo : compilePure inputWires lo k with ⟨loOut, k₁, gLo⟩
      have hlo :
          (evalGates inputs gLo env0) loOut = some (MuxNet.eval lo ρ) := by
        simpa [hLo] using (ihLo (k := k) (env0 := env0) hEnv hIW)
      -- input wires are below `k`, and `gLo` only writes to wires ≥ `k`
      have hgeLo : ∀ g ∈ gLo, k ≤ g.out := by
        intro g hg
        have hg' : g ∈ (compilePure inputWires lo k).2.2 := by
          simpa [hLo] using hg
        exact compilePure_outs_ge_start (inputWires := inputWires) (net := lo) (k := k) g hg'
      have hEnv1 : ∀ v : Fin n, (evalGates inputs gLo env0) (inputWires v) = some (ρ v) := by
        intro v
        have hpres := evalGates_preserve_lt (inputs := inputs) (gs := gLo) (env := env0)
          (k := k) (w := inputWires v) (hw := hIW v) hgeLo
        simpa [hpres] using (hEnv v)
      -- `k₁` is the next fresh wire after compiling `lo`
      have hk₁ : k ≤ k₁ := by
        have hloOut : k ≤ loOut := by
          simpa [hLo] using (compilePure_out_ge_start (inputWires := inputWires) (net := lo) (k := k))
        have hk₁' : k₁ = loOut + 1 := by
          simpa [hLo] using
            (compilePure_next_eq_out_succ (inputWires := inputWires) (net := lo) (k := k))
        simpa [hk₁'] using Nat.le_trans hloOut (Nat.le_succ loOut)
      have hIW' : ∀ v : Fin n, inputWires v < k₁ := fun v => lt_of_lt_of_le (hIW v) hk₁
      rcases hHi : compilePure inputWires hi k₁ with ⟨hiOut, k₂, gHi⟩
      -- Reduce the goal for this mux node to the concrete generated gate list.
      simp [compilePure, hLo, hHi]
      have hhi :
          (evalGates inputs gHi (evalGates inputs gLo env0)) hiOut = some (MuxNet.eval hi ρ) := by
        simpa [hHi] using (ihHi (k := k₁) (env0 := evalGates inputs gLo env0) hEnv1 hIW')
      -- `gHi` writes only to wires ≥ `k₁`, so it preserves `loOut < k₁`
      have hloOut_lt : loOut < k₁ := by
        have hk₁' : k₁ = loOut + 1 := by
          simpa [hLo] using
            (compilePure_next_eq_out_succ (inputWires := inputWires) (net := lo) (k := k))
        simp [hk₁']
      have hgeHi : ∀ g ∈ gHi, k₁ ≤ g.out := by
        intro g hg
        have hg' : g ∈ (compilePure inputWires hi k₁).2.2 := by
          simpa [hHi] using hg
        exact compilePure_outs_ge_start (inputWires := inputWires) (net := hi) (k := k₁) g hg'
      have hlo_pres :
          (evalGates inputs gHi (evalGates inputs gLo env0)) loOut =
            (evalGates inputs gLo env0) loOut := by
        have hpres := evalGates_preserve_lt (inputs := inputs) (gs := gHi)
          (env := evalGates inputs gLo env0) (k := k₁) (w := loOut) hloOut_lt hgeHi
        simpa using hpres
      -- evaluate the final mux gate
      have hSel :
          (evalGates inputs gHi (evalGates inputs gLo env0)) (inputWires v) = some (ρ v) := by
        -- `inputWires v < k ≤ k₁` so also < k₁, hence preserved by `gHi`
        have hvlt : inputWires v < k₁ := lt_of_lt_of_le (hIW v) hk₁
        have hpres := evalGates_preserve_lt (inputs := inputs) (gs := gHi)
          (env := evalGates inputs gLo env0) (k := k₁) (w := inputWires v) hvlt hgeHi
        simpa [hpres] using hEnv1 v
      -- Split evaluation over concatenation and finish by cases on `ρ v`.
      let env2 : WireEnv := evalGates inputs gHi (evalGates inputs gLo env0)
      -- apply the split and compute on the output wire `k₂`
      have hlo2 : env2 loOut = some (MuxNet.eval lo ρ) := by
        simpa [env2, hlo_pres] using hlo
      have hhi2 : env2 hiOut = some (MuxNet.eval hi ρ) := by
        simpa using hhi
      -- final step
      have hSplit :
          evalGates inputs (gLo ++ (gHi ++ [Gate.mux k₂ (inputWires v) loOut hiOut])) env0 k₂ =
            evalGates inputs [Gate.mux k₂ (inputWires v) loOut hiOut] env2 k₂ := by
        simp [env2, evalGates_append]
      cases hv : ρ v <;>
        simp [hSplit, env2, evalGates, Gate.eval, hv, hSel, hlo2, hhi2]

theorem toNetlist_correct {n : Nat} (net : MuxNet.Net n) (ρ : Fin n → Bool) :
    (toNetlist (n := n) net).eval (inputsOf ρ) = some (MuxNet.eval net ρ) := by
  -- Unfold `toNetlist` / `compileMuxNet` and reduce to `eval_compilePure` starting from the input environment.
  let inputs := inputsOf ρ
  let inputWires : Fin n → WireId := fun v => v.val
  let envInputs : WireEnv := evalGates inputs (mkInputGates n) (fun _ => none)
  have hEnvInputs : ∀ v : Fin n, envInputs (inputWires v) = some (ρ v) := by
    intro v
    have hv : v.val < n := v.isLt
    have h := evalGates_mkInputGates (inputs := inputs) (n := n) (i := v.val) hv
    have hv' : (⟨v.val, v.isLt⟩ : Fin n) = v := by cases v; rfl
    have : inputs v.val = ρ v := by
      simp [inputs, inputsOf, v.isLt, hv']
    simpa [envInputs, inputWires, this] using h
  have hIW : ∀ v : Fin n, inputWires v < n := fun v => v.isLt
  -- Expand `compileMuxNet` to expose the `compilePure` triple and apply `eval_compilePure`.
  have hCore :=
    eval_compilePure (inputWires := inputWires) (inputs := inputs) (net := net) (ρ := ρ)
      (k := n) (env0 := envInputs) hEnvInputs hIW
  -- `toNetlist` runs the input gates first, then appends the `compilePure` gates.
  -- Reduce the netlist evaluation to the core lemma via `evalGates_append`.
  simpa [toNetlist, compileMuxNet, Netlist.eval, evalGates_append, initCompileState, inputs, envInputs]
    using hCore

theorem compileMuxNet_correct {n : Nat} (net : MuxNet.Net n) (ρ : Fin n → Bool) :
    let inputs := inputsOf ρ
    let (outWire, s') := compileMuxNet (n := n) net (initCompileState n)
    (evalGates inputs s'.gates (fun _ => none)) outWire = some (MuxNet.eval net ρ) := by
  -- `toNetlist_correct` is exactly this statement after unfolding `Netlist.eval`.
  have h := toNetlist_correct (n := n) (net := net) (ρ := ρ)
  simp [toNetlist, Netlist.eval] at h
  simpa [toNetlist, compileMuxNet, initCompileState, inputsOf] using h

theorem loFToGates_correct {n : Nat} (A : Expr n) (ρ : Fin n → Bool) :
    (toNetlist (n := n) (MuxNet.toMuxNet (n := n) A)).eval (inputsOf ρ) =
      some (LoFPrimary.eval A ρ) := by
  have h := toNetlist_correct (n := n) (net := MuxNet.toMuxNet (n := n) A) (ρ := ρ)
  simpa [MuxNet.eval_toMuxNet] using h

end GateSpec

namespace MuxNet

/-- Compile a `MuxNet.Net n` to a `GateSpec` netlist. -/
def toNetlist {n : Nat} (net : Net n) : GateSpec.Netlist :=
  GateSpec.toNetlist (n := n) net

theorem toNetlist_correct {n : Nat} (net : Net n) (ρ : Fin n → Bool) :
    (toNetlist (n := n) net).eval (GateSpec.inputsOf ρ) = some (eval net ρ) := by
  simpa [toNetlist] using (GateSpec.toNetlist_correct (n := n) (net := net) (ρ := ρ))

end MuxNet

end LoFPrimary
end LoF
end HeytingLean
