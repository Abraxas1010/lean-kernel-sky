# Pipeline Architecture

## Overview

The Lean Kernel → SKY pipeline compiles Lean 4's type-checking algorithms to pure SKY combinators in 25 phases, organized into three layers.

```
┌─────────────────────────────────────────────────────────────────┐
│                         FULL KERNEL                              │
│  Phases 21-25: Environment, δ-reduction, ι-reduction            │
├─────────────────────────────────────────────────────────────────┤
│                      COMPUTATION PLANE                           │
│  Phases 16-20: WHNF, DefEq, Infer as λ-terms                    │
├─────────────────────────────────────────────────────────────────┤
│                        DATA PLANE                                │
│  Phases 7-15: Expr/ULevel encoding, bracket abstraction         │
├─────────────────────────────────────────────────────────────────┤
│                      SKY COMBINATORS                             │
│  Foundation: S, K, Y basis + execution engine                    │
└─────────────────────────────────────────────────────────────────┘
```

## Layer 1: Data Plane (Phases 7-15)

### Purpose
Encode Lean's abstract syntax trees (Expr, ULevel) as combinator terms using Scott encoding.

### Key Modules

| Phase | Module | Description |
|-------|--------|-------------|
| 7 | `UniverseLevel.lean` | Universe level AST + 6-ary Scott encoding |
| 8 | `Expression.lean` | Expression AST + 9-ary Scott encoding |
| 9 | `WHNF.lean` | Native weak-head normal form |
| 10 | `DefEq.lean` | Native definitional equality |
| 11 | `Inductive.lean` | Inductive types and ι-reduction specs |
| 12 | `Infer.lean` | Native type inference |
| 13 | `Environment.lean` | Constant declaration table |
| 14 | `Lean4LeanSKY.lean` | Expr/ULevel → Comb compilation |
| 15 | `Lean4LeanSKYMain.lean` | Data plane demo CLI |

### Scott Encoding

Algebraic data types become λ-abstractions over case handlers:

```lean
-- Expr has 9 constructors → 9-ary encoding
def exprBvar (i : L) : L :=
  lam9 "bv" "mv" "so" "co" "ap" "la" "fo" "le" "li"
    (app (v "bv") i)

def exprApp (fn arg : L) : L :=
  lam9 "bv" "mv" "so" "co" "ap" "la" "fo" "le" "li"
    (app2 (v "ap") fn arg)
```

This allows pattern matching to be expressed as function application:
```
exprCase e onBvar onMvar onSort onConst onApp onLam onForall onLet onLit
  = e onBvar onMvar onSort onConst onApp onLam onForall onLet onLit
```

## Layer 2: Computation Plane (Phases 16-20)

### Purpose
Implement kernel algorithms (WHNF, DefEq, Infer) as pure λ-terms that can be compiled to SKY.

### Key Modules

| Phase | Module | Description |
|-------|--------|-------------|
| 16 | `WHNFSKY.lean` | WHNF as λ-term (β/ζ reduction) |
| 17 | `DefEqSKY.lean` | Definitional equality as λ-term |
| 18 | `InferSKY.lean` | Type inference as λ-term |
| 19 | `KernelSKY.lean` | Compiled bundle + runners |
| 20 | `KernelSKYMain.lean` | Cross-validation CLI |

### Y Combinator Recursion

Recursive algorithms use the fixed-point combinator:

```lean
def whnfSky : L :=
  app .Y
    (lam "self"
      (lam "fuel"
        (lam "e"
          (natCase (v "fuel")
            (v "e")  -- fuel exhausted: return as-is
            (lam "n"
              (optCase (app whnfStepSky (v "e"))
                (v "e")  -- no step: return
                (lam "e'" (app2 (v "self") (v "n") (v "e'")))))))))
```

The Y combinator provides:
```
Y f = f (Y f)
```

This allows `whnfSky` to call itself recursively through the `"self"` binding.

## Layer 3: Full Kernel (Phases 21-25)

### Purpose
Complete the kernel with environment lookup, δ-reduction (constant unfolding), and ι-reduction (inductive eliminators).

### Key Modules

| Phase | Module | Description |
|-------|--------|-------------|
| 21 | `EnvironmentSKY.lean` | Environment as Scott-encoded data |
| 22 | `WHNFDeltaSKY.lean` | δ-reduction (unfold definitions) |
| 23 | `WHNFIotaSKY.lean` | ι-reduction (casesOn/recursor) |
| 24 | `FullKernelSKY.lean` | Combined β/ζ/δ/ι kernel |
| 25 | `FullKernelSKYMain.lean` | Full kernel demo CLI |

### Reduction Forms

| Form | Rule | Implementation |
|------|------|----------------|
| **β** | `(λx.M) N → M[N/x]` | `whnfStepBetaSky` |
| **ζ** | `let x := N in M → M[N/x]` | `whnfStepZetaSky` |
| **δ** | `const c → body` | `whnfStepDeltaSky` |
| **ι** | `casesOn (Cᵢ args) → branchᵢ` | `iotaStepSky` |

## Cross-Validation

Each layer includes a demo CLI that cross-validates:

1. **Native execution**: Run algorithm in Lean
2. **SKY execution**: Compile to combinators, reduce with SKY machine
3. **Compare**: Verify both produce identical results

```bash
lake exe lean4lean_sky_demo --case expr   # Phase 15
lake exe kernel_sky_demo --case all       # Phase 20
lake exe full_kernel_sky_demo --case all  # Phase 25
```

## Compilation Flow

```
Lean Expression
      │
      ▼
┌─────────────┐
│ Scott Encode │  (Data Plane)
└─────────────┘
      │
      ▼
┌─────────────┐
│ λ-term Algo  │  (Computation Plane)
└─────────────┘
      │
      ▼
┌─────────────┐
│ Bracket     │  λx.M → [x]M using S, K
│ Abstraction │
└─────────────┘
      │
      ▼
┌─────────────┐
│ SKY Term    │  Pure S, K, Y applications
└─────────────┘
      │
      ▼
┌─────────────┐
│ SKY Machine │  Fuel-bounded reduction
└─────────────┘
      │
      ▼
   Result
```

## Dependencies

The pipeline depends on:
- **Lean 4**: Host language and type system
- **Mathlib**: Standard library (used sparingly)
- **No external provers**: Self-contained verification

See [04_Dependencies.md](04_Dependencies.md) for version details.
