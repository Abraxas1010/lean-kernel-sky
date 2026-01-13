# Dependencies

## Toolchain

| Component | Version | Purpose |
|-----------|---------|---------|
| Lean 4 | v4.15.0 | Host language |
| Lake | (bundled) | Build system |
| Mathlib | v4.15.0 | Standard library |

## Version Pinning

The toolchain is pinned in `lean-toolchain`:
```
leanprover/lean4:v4.15.0
```

Mathlib is pinned in `lakefile.lean`:
```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"
```

## Lean Options

```lean
package «HeytingLean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,   -- Pretty print λ
    ⟨`autoImplicit, false⟩     -- No implicit arguments
  ]
```

## Module Dependencies

### Import Graph (Simplified)

```
                    HeytingLean.lean (root)
                           │
            ┌──────────────┼──────────────┐
            │              │              │
            ▼              ▼              ▼
      Combinators/    LeanKernel/      Tests/
            │              │              │
    ┌───────┴───────┐     │              │
    │               │     │              │
    ▼               ▼     ▼              ▼
   SKY      BracketAbstr  UniverseLevel  LeanKernelSanity
    │               │     Expression
    │               │     WHNF
    ▼               ▼     DefEq
 SKYExec    SKYMachineBounded  Inductive
                          Infer
                          Environment
                          Lean4LeanSKY
                          WHNFSKY
                          DefEqSKY
                          InferSKY
                          KernelSKY
                          EnvironmentSKY
                          WHNFDeltaSKY
                          WHNFIotaSKY
                          FullKernelSKY
```

### Mathlib Usage

The pipeline uses minimal Mathlib imports:

| Module | Mathlib Imports | Purpose |
|--------|-----------------|---------|
| SKY | `Mathlib.Data.List.Basic` | List utilities |
| Various | `Mathlib.Tactic` | Proof tactics |

Most code is self-contained with no external proof dependencies.

## Axiom Footprint

Standard Lean kernel axioms only:

| Axiom | Description |
|-------|-------------|
| `propext` | `(p ↔ q) → p = q` |
| `Classical.choice` | Nonempty α → α |
| `Quot.sound` | `r a b → Quot.mk r a = Quot.mk r b` |

**No additional axioms introduced by this project.**

## External Dependencies

### Build Requirements

- **C++ compiler**: For Lean's native code generation
- **curl/wget**: For downloading dependencies
- **git**: For fetching Mathlib

### Optional (for visualizations)

```bash
pip install umap-learn plotly numpy scikit-learn
```

## Updating Dependencies

### Update Mathlib

```bash
# Edit lakefile.lean with new version
lake update
lake build
```

### Update Lean

```bash
# Edit lean-toolchain
elan install leanprover/lean4:vX.Y.Z
lake clean
lake build
```

## Compatibility Matrix

| Lean Version | Mathlib Version | Status |
|--------------|-----------------|--------|
| v4.15.0 | v4.15.0 | Verified |
| v4.14.x | v4.14.x | Untested |
| v4.13.x | v4.13.x | Untested |

## License Dependencies

| Dependency | License |
|------------|---------|
| Lean 4 | Apache-2.0 |
| Mathlib | Apache-2.0 |
| This project | Apache-2.0 |

## Reproducible Build

For exact reproduction:

1. Clone at specific commit
2. Use pinned toolchain
3. Run `lake build --wfail`

No floating dependencies or implicit version resolution.
