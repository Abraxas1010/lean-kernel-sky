# Plan: LoF Kernel → SKY Combinators (Full Pipeline)

## Current Problem

The repo only shows the final "Lean Kernel → SKY" compilation, missing the foundational journey:

```
LoF (Laws of Form) → Gates → Lambda → SKY → Lean Kernel
```

## Full Pipeline to Include

### Layer 0: Laws of Form (Distinction)
- **Source**: `LoF/LoFPrimary/` - AIG.lean, GateSpec.lean, MuxNet.lean, etc.
- **Concept**: Spencer-Brown's distinction calculus, boolean circuits from marks

### Layer 1: Gates / Boolean Circuits
- **Source**: `LoF/LoFPrimary/AIG.lean`, `GateSpec.lean`, `MuxNet.lean`
- **Concept**: And-Inverter Graphs, gate specifications, multiplexer networks

### Layer 2: Lambda Calculus
- **Source**: `LoF/Combinators/STLC.lean`, `STLCSKY.lean`
- **Concept**: Simply Typed Lambda Calculus, compilation to SKY

### Layer 3: SKY Combinators
- **Source**: `LoF/Combinators/SKY.lean`, `BracketAbstraction.lean`, `SKYExec.lean`
- **Concept**: S, K, Y basis, bracket abstraction, execution engine

### Layer 4: Fixed Points / Eigenforms
- **Source**: `LoF/Combinators/EigenformBridge.lean`
- **Concept**: Y combinator eigenforms, Curry's paradox, fixed-point semantics

### Layer 5: Heyting / Nucleus
- **Source**: `LoF/Combinators/Heyting/`, `Nucleus.lean`
- **Concept**: Closure operators, Heyting algebras from nuclei

### Layer 6: Category / Topos
- **Source**: `LoF/Combinators/Category/`, `Topos/`
- **Concept**: Multiway categories, sieves, sheaves, Grothendieck topologies

### Layer 7: Lean Kernel Compilation
- **Source**: `LoF/LeanKernel/` (Phases 7-25)
- **Concept**: Compile WHNF/DefEq/Infer to SKY combinators

## Visual Fixes Required

### Current (Wrong)
- Simple scattered points
- Random edges
- Grid background
- Small viewBox

### Correct Style (from Sky_PaperPack)
- **ViewBox**: 1500x900
- **Background**: `#0b0f14`
- **Plot area**: `#0f1721` fill, `#1c2a3a` stroke
- **Edges**: kNN similarity (k=5) with `#3b4b5d`, opacity 0.18
- **Points**: Colored by module family
- **Title + subtitle** explaining the visualization
- **NO GRID** - just connected graph
- **Animated 3D** version

## Files to Include

### From LoFPrimary/
- AIG.lean
- GateSpec.lean
- MuxNet.lean
- Normalization.lean
- Optimize.lean
- Rewrite.lean
- Syntax.lean

### From Combinators/ (additional)
- STLC.lean
- STLCSKY.lean
- EigenformBridge.lean
- Heyting/*.lean
- Category/*.lean (subset)
- Topos/*.lean (subset)
- Rewriting/*.lean

### From Foundation/
- Blocks.lean (already added)
- Soundness.lean (already added)

### From LeanKernel/ (keep existing)
- All Phase 7-25 files

## README Structure

1. **Title + badges**
2. **Why This Matters** - The LoF → Kernel journey
3. **The Generative Pipeline** - Visual diagram showing all layers
4. **Visual Overview** - Pipeline SVG
5. **Proof Visualizations** - 2D/3D UMAP with kNN edges
6. **Quick Start** - Verification command
7. **The Pipeline: LoF → Kernel** - Tables for each layer
8. **Key Theorems** - Bridge theorems between layers
9. **Future Research**
10. **References**

## Implementation Steps

1. Delete current artifacts/visuals
2. Copy all required Lean files
3. Update HeytingLean.lean root import
4. Regenerate visuals with correct kNN style
5. Rewrite README with full narrative
6. Commit and force-push
