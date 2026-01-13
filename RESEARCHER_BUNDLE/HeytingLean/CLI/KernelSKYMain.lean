import HeytingLean.LoF.LeanKernel.KernelSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.WHNFDeltaSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY

/-!
# kernel_sky_demo (Phase 20)

End-to-end demo + cross-validation for the staged computation-plane kernel:

* compile Phase 16/17/18 (WHNF/DefEq/Infer) to closed SKY combinators (Phase 19 bundle),
* run those programs with explicit fuel bounds,
* cross-check against the Lean reference implementations (Phases 9/10/12) on a small set of cases.

This executable is deliberately environment-free (no file I/O, no subprocesses).
-/

namespace HeytingLean.CLI.KernelSKYMain

open System

open HeytingLean.LoF
open HeytingLean.LoF.LeanKernel

abbrev E : Type := Expr Nat Unit Unit Unit

inductive Case where
  | whnf
  | delta
  | iota
  | full
  | defeq
  | infer
  | check
  | env
  | all
deriving DecidableEq, Repr

instance : ToString Case where
  toString
    | .whnf => "whnf"
    | .delta => "delta"
    | .iota => "iota"
    | .full => "full"
    | .defeq => "defeq"
    | .infer => "infer"
    | .check => "check"
    | .env => "env"
    | .all => "all"

structure Cfg where
  caseName : Case := .all
  fuelWhnf : Nat := 10
  fuelDefEq : Nat := 10
  fuelInfer : Nat := 10
  fuelReduce : Nat := 200000
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: kernel_sky_demo [--case all|whnf|delta|iota|full|defeq|infer|check|env] [--fuel-whnf N] [--fuel-defeq N] [--fuel-infer N] [--fuel-reduce N]"
    , ""
    , "Phase 20 demo: compile LeanKernel algorithms to SKY and cross-validate on curated examples."
    , ""
    , "Defaults:"
    , "  --case all"
    , "  --fuel-whnf 10"
    , "  --fuel-defeq 10"
    , "  --fuel-infer 10"
    , "  --fuel-reduce 200000"
    ]

private def parseArgs (argv : List String) : IO Cfg := do
  let rec go (cfg : Cfg) : List String → IO Cfg
    | [] => pure cfg
    | "--help" :: _ => do
        IO.println usage
        throw (IO.userError "help")
    | "--case" :: c :: rest =>
        match c with
        | "all" => go { cfg with caseName := .all } rest
        | "whnf" => go { cfg with caseName := .whnf } rest
        | "delta" => go { cfg with caseName := .delta } rest
        | "iota" => go { cfg with caseName := .iota } rest
        | "full" => go { cfg with caseName := .full } rest
        | "defeq" => go { cfg with caseName := .defeq } rest
        | "infer" => go { cfg with caseName := .infer } rest
        | "check" => go { cfg with caseName := .check } rest
        | "env" => go { cfg with caseName := .env } rest
        | _ => throw <| IO.userError s!"invalid --case value: {c}"
    | "--fuel-whnf" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelWhnf := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-whnf value: {n}"
    | "--fuel-defeq" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelDefEq := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-defeq value: {n}"
    | "--fuel-infer" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelInfer := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-infer value: {n}"
    | "--fuel-reduce" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelReduce := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-reduce value: {n}"
    | x :: _ =>
        throw <| IO.userError s!"unexpected argument: {x}\n\n{usage}"
  go {} argv

private def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure code

private def exprTag (e : E) : String :=
  match e with
  | .bvar _ => "bvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit _ => "lit"

private def expectEq {α : Type} [BEq α] [ToString α] (label : String) (a b : α) : Except String Unit :=
  if a == b then
    .ok ()
  else
    .error s!"{label}: expected {toString a} == {toString b}"

private def mkCasesWhnf : List (String × E) :=
  let idLam : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let arg : E := .lit (.natVal 3)
  let letId : E := .letE 0 .default (.sort .zero) arg (.bvar 0)
  [ ("beta", .app idLam arg)
  , ("zeta", letId)
  ]

private def mkCasesDelta : List (String × E) :=
  let us : List (ULevel Unit Unit) := []
  [ ("unfoldPresentValue", .const 10 us)
  , ("presentNoValue", .const 11 us)
  , ("missingConst", .const 12 us)
  ]

private def mkIotaRules : Inductive.IotaRules Nat :=
  let spec : Inductive.CasesOnSpec Nat :=
    { recursor := 100
      numParams := 1
      ctors :=
        [ { name := 101, numFields := 0 }
        , { name := 102, numFields := 1 } ] }
  { beqName := Nat.beq
    casesOnSpecs := [spec] }

private def mkCasesIota : List (String × E) :=
  let us : List (ULevel Unit Unit) := []
  let casesOn : E := .const 100 us
  let motive : E := .sort .zero
  let zCase : E := .lit (.natVal 0)
  let sCase : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let n : E := .lit (.natVal 7)
  let majorZero : E := .const 101 us
  let majorSucc : E := .app (.const 102 us) n
  let mk (major : E) : E :=
    .app (.app (.app (.app casesOn motive) zCase) sCase) major
  [ ("casesOnZero", mk majorZero)
  , ("casesOnSucc", mk majorSucc)
  ]

private def mkEnvFull : Environment.Env Nat Unit Unit Unit :=
  let us : List (ULevel Unit Unit) := []
  let casesOn : E := .const 100 us
  let motive : E := .sort .zero
  let zCase : E := .lit (.natVal 0)
  let sCase : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let n : E := .lit (.natVal 7)
  let majorSucc : E := .app (.const 102 us) n
  let body : E :=
    .app (.app (.app (.app casesOn motive) zCase) sCase) majorSucc
  { beqName := Nat.beq
    consts := [ Environment.ConstDecl.ofDef 30 (.sort .zero) body ] }

private def mkCasesFull : List (String × E) :=
  let us : List (ULevel Unit Unit) := []
  [ ("deltaThenIota", .const 30 us) ]

private def mkCasesDefEq : List (String × E × E) :=
  let idLam : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let arg : E := .lit (.natVal 3)
  let appId : E := .app idLam arg
  let u1 : ULevel Unit Unit := .max (.succ .zero) .zero
  let u2 : ULevel Unit Unit := .succ .zero
  [ ("beta", appId, arg)
  , ("sortClosedEq", .sort u1, .sort u2)
  ]

private def mkCasesInfer : List (String × E) :=
  let sort0 : E := .sort .zero
  let idLam : E := .lam 0 .default (.sort (.succ .zero)) (.bvar 0)
  let arg : E := .sort .zero
  let appId : E := .app idLam arg
  [ ("sort0", sort0)
  , ("idLam", idLam)
  , ("appId", appId)
  ]

private def mkCasesCheck : List (String × E × E) :=
  let sort0 : E := .sort .zero
  let sort1 : E := .sort (.succ .zero)
  [ ("sort0:sort1", sort0, sort1) ]

private def mkEnv : Environment.Env Nat Unit Unit Unit :=
  { beqName := Nat.beq
    consts :=
      [ Environment.ConstDecl.ofDef 10 (.sort .zero) (.lit (.natVal 7))
      , Environment.ConstDecl.ofType 11 (.sort .zero) ] }

private def runEnvConstCase (cfg : Cfg) (label : String) (env : Environment.Env Nat Unit Unit Unit) (c : Nat) :
    Except String Unit :=
  let us : List (ULevel Unit Unit) := []
  let directTyTag? := (Environment.Env.constType? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env c us).map exprTag
  let directValTag? := (Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env c us).map exprTag
  let typeRes : Except String Unit :=
    match EnvironmentSKY.runConstTypeTagFuel cfg.fuelReduce us env c with
    | none => Except.error s!"env/{label}: SKY constType? tag decode failed"
    | some skyTyTag? =>
        match directTyTag?, skyTyTag? with
        | none, none => Except.ok ()
        | some dt, some st => expectEq s!"env/{label}/type" st dt
        | none, some st => Except.error s!"env/{label}/type: expected none, got {st}"
        | some dt, none => Except.error s!"env/{label}/type: expected {dt}, got none"

  match typeRes with
  | Except.error e => Except.error e
  | Except.ok () =>
      match EnvironmentSKY.runConstValueTagFuel cfg.fuelReduce us env c with
      | none => Except.error s!"env/{label}: SKY constValue? tag decode failed"
      | some skyValTag? =>
          match directValTag?, skyValTag? with
          | none, none => Except.ok ()
          | some dt, some st => expectEq s!"env/{label}/value" st dt
          | none, some st => Except.error s!"env/{label}/value: expected none, got {st}"
          | some dt, none => Except.error s!"env/{label}/value: expected {dt}, got none"

private def runWhnfCase (cfg : Cfg) (k : KernelSKY.Compiled) (name : String) (e : E) :
    Except String Unit :=
  let direct := WHNF.whnf (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg.fuelWhnf e
  match KernelSKY.runWhnfCombFuelWith k cfg.fuelWhnf cfg.fuelReduce e, KernelSKY.compileExprNatUnit? direct with
  | some outC, some directC =>
      match KernelSKY.runIsDefEqCombFuelWith k cfg.fuelDefEq cfg.fuelReduce outC directC with
      | some true => .ok ()
      | some false =>
          match KernelSKY.runWhnfTagFuelWith k cfg.fuelWhnf cfg.fuelReduce e with
          | none => .error s!"whnf/{name}: SKY output mismatch (and tag decode failed)"
          | some tag => .error s!"whnf/{name}: SKY output mismatch (tag={tag}, expectedTag={exprTag direct})"
      | none => .error s!"whnf/{name}: SKY defeq bool decode failed"
  | none, _ => .error s!"whnf/{name}: SKY WHNF comb eval failed"
  | _, none => .error s!"whnf/{name}: failed to compile expected expression to Comb"

private def runDeltaCase (cfg : Cfg) (k : KernelSKY.Compiled) (name : String)
    (env : Environment.Env Nat Unit Unit Unit) (e : E) :
    Except String Unit :=
  let us : List (ULevel Unit Unit) := []
  let direct :=
    WHNF.whnfWithDelta
      (fun c us => Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env c us)
      (Inductive.IotaRules.empty (Name := Nat))
      cfg.fuelWhnf
      e
  match WHNFDeltaSKY.runWhnfDeltaCombFuel cfg.fuelWhnf cfg.fuelReduce us env e, KernelSKY.compileExprNatUnit? direct with
  | some outC, some directC =>
      match KernelSKY.runIsDefEqCombFuelWith k cfg.fuelDefEq cfg.fuelReduce outC directC with
      | some true => .ok ()
      | some false =>
          match WHNFDeltaSKY.runWhnfDeltaTagFuel cfg.fuelWhnf cfg.fuelReduce us env e with
          | none => .error s!"delta/{name}: SKY output mismatch (and tag decode failed)"
          | some tag => .error s!"delta/{name}: SKY output mismatch (tag={tag}, expectedTag={exprTag direct})"
      | none => .error s!"delta/{name}: SKY defeq bool decode failed"
  | none, _ => .error s!"delta/{name}: SKY WHNF-δ comb eval failed"
  | _, none => .error s!"delta/{name}: failed to compile expected expression to Comb"

private def runIotaCase (cfg : Cfg) (k : KernelSKY.Compiled) (name : String)
    (rules : Inductive.IotaRules Nat) (e : E) :
    Except String Unit :=
  let direct :=
    WHNF.whnfWith (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) rules cfg.fuelWhnf e
  let specL :=
    WHNFIotaSKY.Enc.casesOnSpec 100 1 [ (101, 0), (102, 1) ]
  let rulesL :=
    WHNFIotaSKY.Enc.iotaRules [specL]
  match WHNFIotaSKY.runWhnfIotaCombFuel cfg.fuelWhnf cfg.fuelReduce rulesL e, KernelSKY.compileExprNatUnit? direct with
  | some outC, some directC =>
      match KernelSKY.runIsDefEqCombFuelWith k cfg.fuelDefEq cfg.fuelReduce outC directC with
      | some true => .ok ()
      | some false =>
          match WHNFIotaSKY.runWhnfIotaTagFuel cfg.fuelWhnf cfg.fuelReduce rulesL e with
          | none => .error s!"iota/{name}: SKY output mismatch (and tag decode failed)"
          | some tag => .error s!"iota/{name}: SKY output mismatch (tag={tag}, expectedTag={exprTag direct})"
      | none => .error s!"iota/{name}: SKY defeq bool decode failed"
  | none, _ => .error s!"iota/{name}: SKY WHNF-ι comb eval failed"
  | _, none => .error s!"iota/{name}: failed to compile expected expression to Comb"

private def runFullCase (cfg : Cfg) (k : FullKernelSKY.FullCompiled) (name : String)
    (env : Environment.Env Nat Unit Unit Unit) (rules : Inductive.IotaRules Nat) (e : E) :
    Except String Unit :=
  let us : List (ULevel Unit Unit) := []
  let direct :=
    WHNF.whnfWithDelta
      (fun c us => Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env c us)
      rules
      cfg.fuelWhnf
      e
  let specL :=
    WHNFIotaSKY.Enc.casesOnSpec 100 1 [ (101, 0), (102, 1) ]
  let rulesL :=
    WHNFIotaSKY.Enc.iotaRules [specL]
  match EnvironmentSKY.envComb? us env, WHNFIotaSKY.compileClosed? rulesL with
  | some envC, some rulesC =>
      match FullKernelSKY.runWhnfFullCombFuelWith k cfg.fuelWhnf cfg.fuelReduce envC rulesC e,
            Lean4LeanSKY.Enc.compileExprNatUnit? direct with
      | some outC, some directC =>
          match FullKernelSKY.runIsDefEqFullCombFuelWith k cfg.fuelDefEq cfg.fuelReduce envC rulesC outC directC with
          | some true => .ok ()
          | some false =>
              match FullKernelSKY.runWhnfFullTagFuelWith k cfg.fuelWhnf cfg.fuelReduce envC rulesC e with
              | none => .error s!"full/{name}: SKY output mismatch (and tag decode failed)"
              | some tag => .error s!"full/{name}: SKY output mismatch (tag={tag}, expectedTag={exprTag direct})"
          | none => .error s!"full/{name}: SKY defeq bool decode failed"
      | none, _ => .error s!"full/{name}: SKY WHNF-full comb eval failed"
      | _, none => .error s!"full/{name}: failed to compile expected expression to Comb"
  | none, _ => .error s!"full/{name}: failed to compile environment to SKY"
  | _, none => .error s!"full/{name}: failed to compile iota rules to SKY"

private def runDefEqCase (cfg : Cfg) (k : KernelSKY.Compiled) (name : String) (e1 e2 : E) :
    Except String Unit :=
  let direct :=
    DefEq.isDefEq (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg.fuelDefEq e1 e2
  match KernelSKY.runIsDefEqFuelWith k cfg.fuelDefEq cfg.fuelReduce e1 e2 with
  | none => .error s!"defeq/{name}: SKY bool decode failed"
  | some b =>
      expectEq s!"defeq/{name}" b direct

private def runInferCase (cfg : Cfg) (k : KernelSKY.Compiled) (name : String) (e : E) :
    Except String Unit :=
  let cfg0 : Infer.Config Nat Unit Unit Unit := {}
  let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
  let direct :=
    Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e
  match KernelSKY.runInferOptCombFuelWith k cfg.fuelInfer cfg.fuelReduce e with
  | none => .error s!"infer/{name}: SKY infer comb eval failed"
  | some outOpt =>
      let skyTy? := KernelSKY.decodeOptExprCombFuel cfg.fuelReduce outOpt
      match direct, skyTy? with
      | none, none => .ok ()
      | some directTy, some skyTy =>
          match KernelSKY.compileExprNatUnit? directTy with
          | none => .error s!"infer/{name}: failed to compile expected type to Comb"
          | some directTyC =>
              match KernelSKY.runIsDefEqCombFuelWith k cfg.fuelDefEq cfg.fuelReduce skyTy directTyC with
              | some true => .ok ()
              | some false =>
                  match KernelSKY.runInferTagFuelWith k cfg.fuelInfer cfg.fuelReduce e with
                  | none => .error s!"infer/{name}: SKY type mismatch (and tag decode failed)"
                  | some st => .error s!"infer/{name}: SKY type mismatch (gotTag={st}, expectedTag={exprTag directTy})"
              | none => .error s!"infer/{name}: SKY defeq bool decode failed"
      | none, some _ => .error s!"infer/{name}: expected none, got some"
      | some _, none => .error s!"infer/{name}: expected some, got none"

private def runCheckCase (cfg : Cfg) (k : KernelSKY.Compiled) (name : String) (e ty : E) :
    Except String Unit :=
  let cfg0 : Infer.Config Nat Unit Unit Unit := {}
  let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
  let direct :=
    Infer.check (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e ty
  match KernelSKY.runCheckFuelWith k cfg.fuelInfer cfg.fuelReduce e ty with
  | none => .error s!"check/{name}: SKY bool decode failed"
  | some b => expectEq s!"check/{name}" b direct

private def runAll (cfg : Cfg) : IO UInt32 := do
  let needKernel : Bool :=
    match cfg.caseName with
    | .whnf | .defeq | .infer | .check | .all => true
    | _ => false

  let needFull : Bool :=
    match cfg.caseName with
    | .full | .all => true
    | _ => false

  let kernel : Option KernelSKY.Compiled :=
    if needKernel then KernelSKY.compile? else some { whnf := Comb.K, isDefEq := Comb.K, infer := Comb.K, check := Comb.K, emptyCtx := Comb.K }

  let full : Option FullKernelSKY.FullCompiled :=
    if needFull then FullKernelSKY.compileFull? else some { whnf := Comb.K, isDefEq := Comb.K, infer := Comb.K, check := Comb.K, emptyCtx := Comb.K, emptyEnv := Comb.K, emptyRules := Comb.K }

  if needKernel && kernel.isNone then
    die 2 "[kernel_sky_demo] E-COMPILE: failed to compile KernelSKY bundle"
  else if needFull && full.isNone then
    die 2 "[kernel_sky_demo] E-COMPILE: failed to compile FullKernelSKY bundle"
  else
    match kernel, full with
    | some k, some kFull =>

      let whnfErrs :=
        if cfg.caseName == .whnf || cfg.caseName == .all then
          mkCasesWhnf.foldl (init := ([] : List String)) fun acc (nm, e) =>
            match runWhnfCase cfg k nm e with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let deltaErrs :=
        if cfg.caseName == .delta || cfg.caseName == .all then
          mkCasesDelta.foldl (init := ([] : List String)) fun acc (nm, e) =>
            match runDeltaCase cfg k nm mkEnv e with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let iotaErrs :=
        if cfg.caseName == .iota || cfg.caseName == .all then
          mkCasesIota.foldl (init := ([] : List String)) fun acc (nm, e) =>
            match runIotaCase cfg k nm mkIotaRules e with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let fullErrs :=
        if cfg.caseName == .full || cfg.caseName == .all then
          mkCasesFull.foldl (init := ([] : List String)) fun acc (nm, e) =>
            match runFullCase cfg kFull nm mkEnvFull mkIotaRules e with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let defeqErrs :=
        if cfg.caseName == .defeq || cfg.caseName == .all then
          mkCasesDefEq.foldl (init := ([] : List String)) fun acc (nm, e1, e2) =>
            match runDefEqCase cfg k nm e1 e2 with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let inferErrs :=
        if cfg.caseName == .infer || cfg.caseName == .all then
          mkCasesInfer.foldl (init := ([] : List String)) fun acc (nm, e) =>
            match runInferCase cfg k nm e with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let checkErrs :=
        if cfg.caseName == .check || cfg.caseName == .all then
          mkCasesCheck.foldl (init := ([] : List String)) fun acc (nm, e, ty) =>
            match runCheckCase cfg k nm e ty with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let envErrs :=
        if cfg.caseName == .env || cfg.caseName == .all then
          [ ("presentWithValue", 10)
          , ("presentNoValue", 11)
          , ("missing", 12) ].foldl (init := ([] : List String)) fun acc (nm, c) =>
            match runEnvConstCase cfg nm mkEnv c with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let errs :=
        whnfErrs ++ deltaErrs ++ iotaErrs ++ fullErrs ++ defeqErrs ++ inferErrs ++ checkErrs ++ envErrs

      if errs.isEmpty then
        IO.println s!"[kernel_sky_demo] ok (case={cfg.caseName})"
        pure 0
      else
        for e in errs.reverse do
          IO.eprintln s!"[kernel_sky_demo] FAIL {e}"
        die 1 s!"[kernel_sky_demo] FAILED ({errs.length} failing case(s))"
    | _, _ =>
        die 2 "[kernel_sky_demo] E-INTERNAL: missing compiled bundles"

def main (argv : List String) : IO UInt32 := do
  try
    let cfg ← parseArgs argv
    runAll cfg
  catch e =>
    match e with
    | .userError "help" => pure 0
    | _ => die 1 s!"[kernel_sky_demo] FAILED: {e}"

end HeytingLean.CLI.KernelSKYMain

open HeytingLean.CLI.KernelSKYMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.KernelSKYMain.main args
