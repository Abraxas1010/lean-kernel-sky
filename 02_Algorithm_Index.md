# Algorithm Index

## Core Algorithms

This document indexes the key algorithms implemented in the Lean Kernel → SKY pipeline.

## Weak-Head Normal Form (WHNF)

### Native Implementation
**File**: `HeytingLean/LoF/LeanKernel/WHNF.lean`

```lean
def whnf (e : Expr) : Expr
```

Reduces an expression to weak-head normal form, applying:
- β-reduction: `(λx.M) N → M[N/x]`
- ζ-reduction: `let x := N in M → M[N/x]`

### SKY Implementation
**File**: `HeytingLean/LoF/LeanKernel/WHNFSKY.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `whnfStepSky` | `L` | Single-step WHNF reduction |
| `whnfSky` | `L` | Full WHNF with fuel |
| `instantiate1Sky` | `L` | Substitute de Bruijn index 0 |
| `liftLooseBVarsSky` | `L` | Lift free variables |

### Algorithm Structure

```
whnfSky = Y (λself fuel e.
  natCase fuel
    e                           -- fuel exhausted
    (λn. optCase (whnfStepSky e)
      e                         -- no reduction
      (λe'. self n e')))        -- recurse
```

---

## Definitional Equality (DefEq)

### Native Implementation
**File**: `HeytingLean/LoF/LeanKernel/DefEq.lean`

```lean
def isDefEq (e1 e2 : Expr) : Bool
```

Checks if two expressions are definitionally equal.

### SKY Implementation
**File**: `HeytingLean/LoF/LeanKernel/DefEqSKY.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `ulevelDefEq` | `L` | Universe level equality |
| `isDefEqSky` | `L` | Full definitional equality |
| `exprStructEq` | `L` | Structural equality check |

### Algorithm Structure

```
isDefEqSky = Y (λself fuel e1 e2.
  let e1' = whnfSky fuel e1
  let e2' = whnfSky fuel e2
  exprCase e1'
    (λi. exprCase e2' (λj. natEq i j) ...)  -- BVar
    ...
    (λfn1 arg1. exprCase e2'               -- App
      ...
      (λfn2 arg2. and (self fuel fn1 fn2)
                      (self fuel arg1 arg2))
      ...))
```

---

## Type Inference (Infer)

### Native Implementation
**File**: `HeytingLean/LoF/LeanKernel/Infer.lean`

```lean
def infer (ctx : Context) (e : Expr) : Option Expr
```

Infers the type of an expression in a given context.

### SKY Implementation
**File**: `HeytingLean/LoF/LeanKernel/InferSKY.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `inferSky` | `L` | Type inference |
| `checkSky` | `L` | Type checking (infer + DefEq) |
| `ctxLookup` | `L` | Context variable lookup |

### Algorithm Structure

```
inferSky = Y (λself fuel ctx e.
  exprCase e
    (λi. ctxLookup ctx i)           -- BVar: lookup in context
    (λ_. none)                       -- MVar: not supported
    (λu. some (exprSort (uSucc u)))  -- Sort: type is Sort (u+1)
    (λname _. envLookup? name)       -- Const: lookup in env
    (λfn arg.                        -- App: infer fn, check Pi
      bind (self fuel ctx fn) (λfnTy.
        bind (whnfSky fuel fnTy) ...))
    ...)
```

---

## Environment Operations

### File: `HeytingLean/LoF/LeanKernel/EnvironmentSKY.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `envLookup?` | `L` | Look up constant by name |
| `constType?` | `L` | Get constant's type |
| `constValue?` | `L` | Get constant's value (if def) |

### Environment Encoding

The environment is encoded as a Scott-encoded association list:
```lean
def envCons (name : L) (info : L) (rest : L) : L :=
  lam2 "nil" "cons" (app3 (v "cons") name info rest)
```

---

## δ-Reduction (Constant Unfolding)

### File: `HeytingLean/LoF/LeanKernel/WHNFDeltaSKY.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `whnfStepDeltaSky` | `L` | Single δ-step |
| `whnfDeltaSky` | `L` | WHNF with δ-unfolding |

### Algorithm

```
whnfStepDeltaSky env e =
  exprCase e
    ...
    (λname uparams.                    -- Const
      bind (envLookup? env name) (λinfo.
        constInfoCase info
          (λ_ body. some (instantiateUParams body uparams))  -- Definition
          (λ_. none)                                          -- Axiom
          ...))
    ...
```

---

## ι-Reduction (Inductive Eliminators)

### File: `HeytingLean/LoF/LeanKernel/WHNFIotaSKY.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `iotaStepSky` | `L` | Single ι-step |
| `whnfIotaSky` | `L` | WHNF with ι-reduction |
| `getRecAppArgs` | `L` | Extract recursor arguments |

### Algorithm

ι-reduction handles `casesOn` and recursors:
```
Nat.casesOn motive n onZero onSucc
  where n = Nat.succ m
  → onSucc m
```

The algorithm:
1. Detect recursor application
2. Extract discriminant
3. Match constructor
4. Apply appropriate branch

---

## Full Kernel

### File: `HeytingLean/LoF/LeanKernel/FullKernelSKY.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `whnfFullSky` | `L` | WHNF with β/ζ/δ/ι |
| `isDefEqFullSky` | `L` | DefEq with full reduction |
| `inferFullSky` | `L` | Infer with full kernel |

### Combined Reduction

```lean
def whnfFullStepSky (env : L) (e : L) : L :=
  optOr (whnfStepBetaSky e)
    (optOr (whnfStepZetaSky e)
      (optOr (whnfStepDeltaSky env e)
        (iotaStepSky env e)))
```

---

## Bracket Abstraction

### File: `HeytingLean/LoF/Combinators/BracketAbstraction.lean`

Converts λ-terms to SKY combinators:

| Rule | Pattern | Result |
|------|---------|--------|
| Var | `[x]x` | `I` = `S K K` |
| Const | `[x]c` | `K c` |
| App | `[x](M N)` | `S ([x]M) ([x]N)` |

### Optimizations

- **η-reduction**: `[x](M x)` where x not in M → `M`
- **K-optimization**: `[x](K M)` → `K M` when x not free

---

## SKY Execution Engine

### File: `HeytingLean/LoF/Combinators/SKYExec.lean`

| Definition | Type | Description |
|------------|------|-------------|
| `reduce` | `Comb → Nat → Comb` | Fuel-bounded reduction |
| `step` | `Comb → Option Comb` | Single reduction step |

### Reduction Rules

```
S f g x → f x (g x)
K x y   → x
Y f     → f (Y f)
```

### File: `HeytingLean/LoF/Combinators/SKYMachineBounded.lean`

Hardware-friendly execution with:
- Fixed-size node pool
- Explicit fuel bounds
- State machine interface
