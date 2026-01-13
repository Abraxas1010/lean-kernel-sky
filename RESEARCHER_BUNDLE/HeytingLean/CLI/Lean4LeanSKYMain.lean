import Lean.Data.Json
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

/-!
# lean4lean_sky_demo (Phase 15)

End-to-end “data plane” demo for the staged LeanKernel → SKY bridge:

* build a small staged kernel object (`Expr` or `ULevel`),
* compile it to a closed SKY term via Scott encoding + bracket abstraction (Phase 14),
* run a SKY reducer to extract a constructor tag,
* optionally export a bounded heap+stack machine image (for FPGA demos).
-/

namespace HeytingLean.CLI.Lean4LeanSKYMain

open System
open Lean

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

abbrev OracleRef := _root_.Unit

inductive Kind where
  | expr
  | ulevel
deriving DecidableEq, Repr

instance : ToString Kind where
  toString
    | .expr => "expr"
    | .ulevel => "ulevel"

structure Cfg where
  kind : Kind := .expr
  caseName : String := "lit7"
  fuel : Nat := 5000
  maxNodes : Nat := 50000
  exportFiles : Bool := false
  outDir : FilePath := "dist" / "lean4lean_sky_demo"
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: lean4lean_sky_demo [--kind expr|ulevel] [--case NAME] [--fuel N] [--max-nodes N] [--export] [--out DIR]"
    , ""
    , "Phase 15 demo: compile staged LeanKernel data to SKY and extract constructor tags."
    , ""
    , "Defaults:"
    , "  --kind expr"
    , "  --case lit7"
    , "  --fuel 5000"
    , "  --max-nodes 50000"
    , ""
    , "Expr cases:"
    , "  lit7 | forallNatNat | lamId"
    , ""
    , "ULevel cases:"
    , "  imax10 | max10 | succ0"
    ]

private def parseArgs (argv : List String) : IO Cfg := do
  let rec go (cfg : Cfg) : List String → IO Cfg
    | [] => pure cfg
    | "--help" :: _ => do
        IO.println usage
        throw (IO.userError "help")
    | "--kind" :: k :: rest =>
        match k with
        | "expr" => go { cfg with kind := .expr } rest
        | "ulevel" => go { cfg with kind := .ulevel } rest
        | _ => throw <| IO.userError s!"invalid --kind value: {k}"
    | "--case" :: v :: rest =>
        go { cfg with caseName := v } rest
    | "--fuel" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuel := v } rest
        | none => throw <| IO.userError s!"invalid --fuel value: {n}"
    | "--max-nodes" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with maxNodes := v } rest
        | none => throw <| IO.userError s!"invalid --max-nodes value: {n}"
    | "--export" :: rest =>
        go { cfg with exportFiles := true } rest
    | "--out" :: d :: rest =>
        go { cfg with outDir := FilePath.mk d } rest
    | x :: _ =>
        throw <| IO.userError s!"unexpected argument: {x}\n\n{usage}"
  go {} argv

private def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure code

private def mkOutDir (outDir : FilePath) : IO (Except String Unit) := do
  try
    IO.FS.createDirAll outDir
    pure (Except.ok ())
  catch e =>
    pure (Except.error s!"failed to create output directory {outDir}: {e}")

private def writeFileSafe (path : FilePath) (contents : String) : IO Unit := do
  IO.FS.writeFile path contents

private def nodeToJson (n : SKYGraph.Node OracleRef) : Json :=
  match n with
  | .combK => Json.mkObj [("tag", Json.str "K")]
  | .combS => Json.mkObj [("tag", Json.str "S")]
  | .combY => Json.mkObj [("tag", Json.str "Y")]
  | .app f a => Json.mkObj [("tag", Json.str "app"), ("f", toJson f), ("a", toJson a)]
  | .oracle _ => Json.mkObj [("tag", Json.str "oracle")]

private def stateToJson (maxNodes fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  Json.mkObj
    [ ("maxNodes", toJson maxNodes)
    , ("fuel", toJson fuel)
    , ("nodesUsed", toJson s.nodes.size)
    , ("focus", toJson s.focus)
    , ("stack", toJson s.stack.toArray)
    , ("nodes", Json.arr (s.nodes.map nodeToJson))
    ]

private def oracleEvalFalse : OracleRef → Bool := fun _ => false

private def matchesCombAt (s : SKYMachineBounded.State OracleRef) (id : Nat) : Comb → Bool
  | .K =>
      match s.node? id with
      | some .combK => true
      | _ => false
  | .S =>
      match s.node? id with
      | some .combS => true
      | _ => false
  | .Y =>
      match s.node? id with
      | some .combY => true
      | _ => false
  | .app f a =>
      match s.node? id with
      | some (.app fId aId) => matchesCombAt s fId f && matchesCombAt s aId a
      | _ => false

private def combHeadArgsRev : Comb → Comb × List Comb
  | .app f a =>
      let (h, args) := combHeadArgsRev f
      (h, a :: args)
  | t => (t, [])

private def all2 (p : Nat → Comb → Bool) : List Nat → List Comb → Bool
  | [], [] => true
  | i :: is, t :: ts => p i t && all2 p is ts
  | _, _ => false

private def matchesCombSpine (s : SKYMachineBounded.State OracleRef) (focus : Nat) (stack : List Nat) (t : Comb) : Bool :=
  let (head, argsRev) := combHeadArgsRev t
  let args := argsRev.reverse
  matchesCombAt s focus head && all2 (fun i a => matchesCombAt s i a) stack args

private def kindTagTermToString? (k : Kind) (t : Comb) : Option String :=
  match k with
  | .ulevel =>
      let tagZero := Comb.K
      let tagSucc := Comb.S
      let tagMax := Comb.Y
      let tagIMax := Comb.app Comb.K Comb.K
      let tagParam := Comb.app Comb.K Comb.S
      let tagMVar := Comb.app Comb.K Comb.Y
      if t = tagZero then some "zero"
      else if t = tagSucc then some "succ"
      else if t = tagMax then some "max"
      else if t = tagIMax then some "imax"
      else if t = tagParam then some "param"
      else if t = tagMVar then some "mvar"
      else none
  | .expr =>
      let tagBVar := Comb.K
      let tagMVar := Comb.S
      let tagSort := Comb.Y
      let tagConst := Comb.app Comb.K Comb.K
      let tagApp := Comb.app Comb.K Comb.S
      let tagLam := Comb.app Comb.K Comb.Y
      let tagForall := Comb.app Comb.S Comb.K
      let tagLet := Comb.app Comb.S Comb.S
      let tagLit := Comb.app Comb.S Comb.Y
      if t = tagBVar then some "bvar"
      else if t = tagMVar then some "mvar"
      else if t = tagSort then some "sort"
      else if t = tagConst then some "const"
      else if t = tagApp then some "app"
      else if t = tagLam then some "lam"
      else if t = tagForall then some "forallE"
      else if t = tagLet then some "letE"
      else if t = tagLit then some "lit"
      else none

private def buildCase (cfg : Cfg) :
    Except String (Comb × Comb × Comb) := do
  /-
  Returns:
  * `encoded` : Scott-encoded data as a closed SKY term,
  * `decodeTerm` : SKY term that eliminates to a tag term,
  * `tagTerm` : reduced (fuel-bounded) tag term.
  -/
  match cfg.kind with
  | .expr =>
      let e : Expr Nat Unit Unit Unit ←
        match cfg.caseName with
        | "lit7" => pure <| .lit (.natVal 7)
        | "forallNatNat" => pure <| .forallE 0 .default (.const 100 []) (.const 100 [])
        | "lamId" => pure <| .lam 0 .default (.sort .zero) (.bvar 0)
        | other => throw s!"unknown expr --case: {other}"
      match Lean4LeanSKY.Enc.compileExprNatUnit? e with
      | none => throw "internal error: failed to compile Expr to SKY"
      | some encoded =>
          let decodeTerm := Lean4LeanSKY.Decode.exprDecodeTerm encoded
          let tagTerm := Lean4LeanSKY.Decode.exprTagTermFuel cfg.fuel encoded
          pure (encoded, decodeTerm, tagTerm)
  | .ulevel =>
      let u : ULevel Unit Unit ←
        match cfg.caseName with
        | "imax10" => pure <| .imax (.succ .zero) .zero
        | "max10" => pure <| .max (.succ .zero) .zero
        | "succ0" => pure <| .succ .zero
        | other => throw s!"unknown ulevel --case: {other}"
      match Lean4LeanSKY.Enc.compileULevelNatUnit? u with
      | none => throw "internal error: failed to compile ULevel to SKY"
      | some encoded =>
          let decodeTerm := Lean4LeanSKY.Decode.ulevelDecodeTerm encoded
          let tagTerm := Lean4LeanSKY.Decode.ulevelTagTermFuel cfg.fuel encoded
          pure (encoded, decodeTerm, tagTerm)

private def exportMachine (cfg : Cfg) (decodeTerm expectedTagTerm : Comb) : IO UInt32 := do
  match (← mkOutDir cfg.outDir) with
  | .error msg => return (← die 2 s!"[lean4lean_sky_demo] E-OUTDIR: {msg}")
  | .ok () => pure ()

  let s0 ←
    match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes decodeTerm with
    | some s => pure s
    | none =>
        return (← die 1
          s!"[lean4lean_sky_demo] out of heap during compilation; increase --max-nodes (currently {cfg.maxNodes})")

  let rec runWithStats (fuel : Nat) (s : SKYMachineBounded.State OracleRef)
      (stepsTaken maxStack maxNodesUsed : Nat) :
      Nat × Nat × Nat × SKYMachineBounded.State.StepResult OracleRef :=
    match fuel with
    | 0 => (stepsTaken, maxStack, maxNodesUsed, .halted s)
    | Nat.succ n =>
        match SKYMachineBounded.State.step (OracleRef := OracleRef) oracleEvalFalse cfg.maxNodes s with
        | .progress s' =>
            let maxStack' := Nat.max maxStack s'.stack.length
            let maxNodesUsed' := Nat.max maxNodesUsed s'.nodes.size
            runWithStats n s' (stepsTaken + 1) maxStack' maxNodesUsed'
        | .halted s' => (stepsTaken, maxStack, maxNodesUsed, .halted s')
        | .outOfHeap s' => (stepsTaken, maxStack, maxNodesUsed, .outOfHeap s')

  let (stepsTaken, maxStack, maxNodesUsed, out) :=
    runWithStats cfg.fuel s0 0 s0.stack.length s0.nodes.size

  let (statusTag, finalState) :=
    match out with
    | .progress s => ("progress", s)
    | .halted s => ("halted", s)
    | .outOfHeap s => ("outOfHeap", s)

  if statusTag = "outOfHeap" then
    return (← die 1 s!"[lean4lean_sky_demo] machine ran out of heap (maxNodes={cfg.maxNodes}); increase --max-nodes")

  let ok := matchesCombSpine finalState finalState.focus finalState.stack expectedTagTerm
  if ok = false then
    return (← die 1 s!"[lean4lean_sky_demo] machine output does not match expected tag term; try increasing --fuel")

  let cfgPath := cfg.outDir / "config.repr.txt"
  let machinePath := cfg.outDir / "machine.json"
  let finalPath := cfg.outDir / "final.json"
  let expectedPath := cfg.outDir / "expected.txt"

  let machineJson := stateToJson cfg.maxNodes cfg.fuel s0
  let finalJson := stateToJson cfg.maxNodes cfg.fuel finalState

  try
    writeFileSafe cfgPath (reprStr cfg ++ "\n")
    writeFileSafe machinePath (toString machineJson ++ "\n")
    writeFileSafe finalPath (toString finalJson ++ "\n")
    writeFileSafe expectedPath (String.intercalate "\n"
      [ s!"kind={cfg.kind}"
      , s!"case={cfg.caseName}"
      , s!"fuel={cfg.fuel}"
      , s!"max_nodes={cfg.maxNodes}"
      , s!"expected_tag_term={reprStr expectedTagTerm}"
      , s!"steps_taken={stepsTaken}"
      , s!"max_stack={maxStack}"
      , s!"max_nodes_used={maxNodesUsed}"
      ] ++ "\n")
  catch e =>
    return (← die 3 s!"[lean4lean_sky_demo] E-WRITE: failed to write outputs: {e}")

  IO.println s!"[lean4lean_sky_demo] wrote {machinePath}"
  IO.println s!"[lean4lean_sky_demo] wrote {finalPath}"
  IO.println s!"[lean4lean_sky_demo] ok"
  pure 0

def main (argv : List String) : IO UInt32 := do
  try
    let cfg ← parseArgs argv
    match buildCase cfg with
    | .error msg => return (← die 1 s!"[lean4lean_sky_demo] {msg}")
    | .ok (_encoded, decodeTerm, tagTerm) =>
        let tagStr := (kindTagTermToString? cfg.kind tagTerm).getD "unknown"
        IO.println s!"[lean4lean_sky_demo] kind={cfg.kind} case={cfg.caseName}"
        IO.println s!"[lean4lean_sky_demo] tag={tagStr} tagTerm={reprStr tagTerm}"
        if cfg.exportFiles then
          exportMachine cfg decodeTerm tagTerm
        else
          pure 0
  catch e =>
    match e with
    | .userError "help" => pure 0
    | _ => die 1 s!"[lean4lean_sky_demo] FAILED: {e}"

end HeytingLean.CLI.Lean4LeanSKYMain

open HeytingLean.CLI.Lean4LeanSKYMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.Lean4LeanSKYMain.main args
