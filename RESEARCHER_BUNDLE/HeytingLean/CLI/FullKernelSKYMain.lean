import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY

/-!
# full_kernel_sky_demo (Phase 25)

Executable demo + cross-validation for the *full* computation-plane kernel:
- β/ζ/δ/ι WHNF via `FullKernelSKY`,
- definitional equality + inference/checking layered on top of that WHNF,
- cross-validated against the native reference implementations.

This executable is deliberately pure (no file I/O, no subprocesses).
-/

namespace HeytingLean.CLI.FullKernelSKYMain

open System

open HeytingLean.LoF
open HeytingLean.LoF.LeanKernel

abbrev E : Type := Expr Nat Unit Unit Unit

inductive Case where
  | whnf
  | infer
  | check
  | all
deriving DecidableEq, Repr

instance : ToString Case where
  toString
    | .whnf => "whnf"
    | .infer => "infer"
    | .check => "check"
    | .all => "all"

structure Cfg where
  caseName : Case := .all
  fuelWhnf : Nat := 20
  fuelDefEq : Nat := 20
  fuelInfer : Nat := 20
  fuelReduce : Nat := 400000
deriving Repr

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: full_kernel_sky_demo [--case all|whnf|infer|check] [--fuel-whnf N] [--fuel-defeq N] [--fuel-infer N] [--fuel-reduce N]"
    , ""
    , "Phase 25 demo: compile FullKernelSKY (β/ζ/δ/ι + Infer/Check) to SKY and cross-validate."
    , ""
    , "Defaults:"
    , "  --case all"
    , "  --fuel-whnf 20"
    , "  --fuel-defeq 20"
    , "  --fuel-infer 20"
    , "  --fuel-reduce 400000"
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
        | "infer" => go { cfg with caseName := .infer } rest
        | "check" => go { cfg with caseName := .check } rest
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

/-! ## Environment + rules shared by all Phase 25 cases -/

private def mkCasesOnSpec : Inductive.CasesOnSpec Nat :=
  { recursor := 100
    numParams := 1
    ctors :=
      [ { name := 101, numFields := 0 }
      , { name := 102, numFields := 1 } ] }

private def mkRules : Inductive.IotaRules Nat :=
  { beqName := Nat.beq
    casesOnSpecs := [mkCasesOnSpec] }

private def mkRulesL : WHNFSKY.L :=
  let specL := WHNFIotaSKY.Enc.casesOnSpec 100 1 [ (101, 0), (102, 1) ]
  WHNFIotaSKY.Enc.iotaRules [specL]

private def mkEnv : Environment.Env Nat Unit Unit Unit :=
  let us : List (ULevel Unit Unit) := []
  let natName : Nat := 200
  let natTy : E := .const natName us
  let natZero : E := .const 101 us
  let natSucc : E := .const 102 us
  let natSuccTy : E := .forallE 0 .default natTy natTy

  let casesOn : E := .const 100 us
  let motive : E := .sort .zero
  let zCase : E := .lit (.natVal 0)
  let sCase : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let n : E := .lit (.natVal 7)
  let majorSucc : E := .app natSucc n
  let deltaThenIotaBody : E := .app (.app (.app (.app casesOn motive) zCase) sCase) majorSucc

  { beqName := Nat.beq
    casesOnSpecs := [mkCasesOnSpec]
    consts :=
      [ Environment.ConstDecl.ofType natName (.sort .zero)
      , Environment.ConstDecl.ofType 101 natTy
      , Environment.ConstDecl.ofType 102 natSuccTy
      -- recursor constant (type is irrelevant for WHNF-only demos here)
      , Environment.ConstDecl.ofType 100 (.sort .zero)
      -- pure δ-unfolding demo: `def 32 := Nat.zero`
      , Environment.ConstDecl.ofDef 32 natTy natZero
      -- δ then ι demo: `def 30 := Nat.casesOn ... (Nat.succ n)`
      , Environment.ConstDecl.ofDef 30 (.sort .zero) deltaThenIotaBody ] }

/-! ## Curated test cases -/

private def mkCasesWhnf : List (String × E) :=
  let idLam : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let arg : E := .lit (.natVal 3)
  let letId : E := .letE 0 .default (.sort .zero) arg (.bvar 0)

  let us : List (ULevel Unit Unit) := []
  let casesOn : E := .const 100 us
  let motive : E := .sort .zero
  let zCase : E := .lit (.natVal 0)
  let sCase : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let n : E := .lit (.natVal 7)
  let majorZero : E := .const 101 us
  let majorSucc : E := .app (.const 102 us) n
  let mkCasesOn (major : E) : E :=
    .app (.app (.app (.app casesOn motive) zCase) sCase) major

  let natName : Nat := 200
  let natTy : E := .const natName us
  let letNatZero : E := .letE 0 .default natTy (.const 101 us) (.bvar 0)

  [ ("beta", .app idLam arg)
  , ("zeta", letId)
  , ("iota_zero", mkCasesOn majorZero)
  , ("iota_succ", mkCasesOn majorSucc)
  , ("delta_only", .const 32 us)
  , ("delta_then_iota", .const 30 us)
  , ("zeta_with_const", letNatZero)
  ]

private def mkCasesInfer : List (String × E) :=
  let us : List (ULevel Unit Unit) := []
  let sort0 : E := .sort .zero
  let idLam : E := .lam 0 .default (.sort (.succ .zero)) (.bvar 0)
  let natZero : E := .const 101 us
  let natSuccZero : E := .app (.const 102 us) natZero
  [ ("sort0", sort0)
  , ("idLam", idLam)
  , ("nat_zero", natZero)
  , ("nat_succ_zero", natSuccZero)
  ]

private def mkCasesCheck : List (String × E × E) :=
  let us : List (ULevel Unit Unit) := []
  let sort0 : E := .sort .zero
  let sort1 : E := .sort (.succ .zero)
  let natTy : E := .const 200 us
  let natZero : E := .const 101 us
  let natSuccZero : E := .app (.const 102 us) natZero
  let deltaOnly : E := .const 32 us
  [ ("sort0:sort1", sort0, sort1)
  , ("nat_zero:Nat", natZero, natTy)
  , ("nat_succ_zero:Nat", natSuccZero, natTy)
  , ("delta_only:Nat", deltaOnly, natTy)
  ]

/-! ## Cross-validation runners -/

private def runWhnfCase (cfg : Cfg) (k : FullKernelSKY.FullCompiled)
    (envC rulesC : Comb) (name : String) (env : Environment.Env Nat Unit Unit Unit) (rules : Inductive.IotaRules Nat) (e : E) :
    Except String Unit :=
  let direct :=
    WHNF.whnfWithDelta
      (fun c us => Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env c us)
      rules
      cfg.fuelWhnf
      e
  match FullKernelSKY.runWhnfFullCombFuelWith k cfg.fuelWhnf cfg.fuelReduce envC rulesC e,
        Lean4LeanSKY.Enc.compileExprNatUnit? direct with
  | some outC, some directC =>
      match FullKernelSKY.runIsDefEqFullCombFuelWith k cfg.fuelDefEq cfg.fuelReduce envC rulesC outC directC with
      | some true => .ok ()
      | some false =>
          match FullKernelSKY.runWhnfFullTagFuelWith k cfg.fuelWhnf cfg.fuelReduce envC rulesC e with
          | none => .error s!"whnf/{name}: SKY output mismatch (and tag decode failed)"
          | some tag => .error s!"whnf/{name}: SKY output mismatch (tag={tag}, expectedTag={exprTag direct})"
      | none => .error s!"whnf/{name}: SKY defeq bool decode failed"
  | none, _ => .error s!"whnf/{name}: SKY WHNF comb eval failed"
  | _, none => .error s!"whnf/{name}: failed to compile expected expression to Comb"

private def runInferCase (cfg : Cfg) (k : FullKernelSKY.FullCompiled)
    (envC rulesC : Comb) (name : String) (env : Environment.Env Nat Unit Unit Unit) (e : E) :
    Except String Unit :=
  let cfg0 := (Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env)
  let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
  let direct := Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e
  match FullKernelSKY.runInferFullOptCombFuelWith k cfg.fuelInfer cfg.fuelReduce envC rulesC e with
  | none => .error s!"infer/{name}: SKY infer comb eval failed"
  | some outOpt =>
      let skyTy? := FullKernelSKY.decodeOptExprCombFuel cfg.fuelReduce outOpt
      match direct, skyTy? with
      | none, none => .ok ()
      | some directTy, some skyTy =>
          match Lean4LeanSKY.Enc.compileExprNatUnit? directTy with
          | none => .error s!"infer/{name}: failed to compile expected type to Comb"
          | some directTyC =>
              match FullKernelSKY.runIsDefEqFullCombFuelWith k cfg.fuelDefEq cfg.fuelReduce envC rulesC skyTy directTyC with
              | some true => .ok ()
              | some false =>
                  match FullKernelSKY.runInferFullTagFuelWith k cfg.fuelInfer cfg.fuelReduce envC rulesC e with
                  | none => .error s!"infer/{name}: SKY type mismatch (and tag decode failed)"
                  | some st => .error s!"infer/{name}: SKY type mismatch (gotTag={st}, expectedTag={exprTag directTy})"
              | none => .error s!"infer/{name}: SKY defeq bool decode failed"
      | none, some _ => .error s!"infer/{name}: expected none, got some"
      | some _, none => .error s!"infer/{name}: expected some, got none"

private def runCheckCase (cfg : Cfg) (k : FullKernelSKY.FullCompiled)
    (envC rulesC : Comb) (name : String) (env : Environment.Env Nat Unit Unit Unit) (e ty : E) :
    Except String Unit :=
  let cfg0 := (Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env)
  let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
  let direct := Infer.check (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e ty
  match FullKernelSKY.runCheckFullFuelWith k cfg.fuelInfer cfg.fuelReduce envC rulesC e ty with
  | none => .error s!"check/{name}: SKY bool decode failed"
  | some b => expectEq s!"check/{name}" b direct

private def runAll (cfg : Cfg) : IO UInt32 := do
  let env := mkEnv
  let rules := mkRules
  let us : List (ULevel Unit Unit) := []
  let rulesL := mkRulesL

  match FullKernelSKY.compileFull?, EnvironmentSKY.envComb? us env, WHNFIotaSKY.compileClosed? rulesL with
  | some k, some envC, some rulesC =>
      let whnfErrs :=
        if cfg.caseName == .whnf || cfg.caseName == .all then
          mkCasesWhnf.foldl (init := ([] : List String)) fun acc (nm, e) =>
            match runWhnfCase cfg k envC rulesC nm env rules e with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let inferErrs :=
        if cfg.caseName == .infer || cfg.caseName == .all then
          mkCasesInfer.foldl (init := ([] : List String)) fun acc (nm, e) =>
            match runInferCase cfg k envC rulesC nm env e with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let checkErrs :=
        if cfg.caseName == .check || cfg.caseName == .all then
          mkCasesCheck.foldl (init := ([] : List String)) fun acc (nm, e, ty) =>
            match runCheckCase cfg k envC rulesC nm env e ty with
            | .ok () => acc
            | .error msg => msg :: acc
        else
          []

      let errs := whnfErrs ++ inferErrs ++ checkErrs

      if errs.isEmpty then
        IO.println s!"[full_kernel_sky_demo] ok (case={cfg.caseName})"
        pure 0
      else
        for e in errs.reverse do
          IO.eprintln s!"[full_kernel_sky_demo] FAIL {e}"
        die 1 s!"[full_kernel_sky_demo] FAILED ({errs.length} failing case(s))"
  | none, _, _ => die 2 "[full_kernel_sky_demo] E-COMPILE: failed to compile FullKernelSKY bundle"
  | _, none, _ => die 2 "[full_kernel_sky_demo] E-COMPILE: failed to compile environment to SKY"
  | _, _, none => die 2 "[full_kernel_sky_demo] E-COMPILE: failed to compile iota rules to SKY"

def main (argv : List String) : IO UInt32 := do
  try
    let cfg ← parseArgs argv
    runAll cfg
  catch e =>
    match e with
    | .userError "help" => pure 0
    | _ => die 1 s!"[full_kernel_sky_demo] FAILED: {e}"

end HeytingLean.CLI.FullKernelSKYMain

open HeytingLean.CLI.FullKernelSKYMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FullKernelSKYMain.main args
