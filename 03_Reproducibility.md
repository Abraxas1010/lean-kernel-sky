# Reproducibility Guide

## Quick Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_lean_kernel.sh
```

This single command:
1. Checks for `sorry`/`admit` (must be zero)
2. Builds the library with `--wfail`
3. Builds all three demo executables
4. Runs cross-validation tests
5. Emits reproducibility hashes

Expected output:
```
========================================
VERIFICATION PASSED
========================================

Summary:
  - Library:      PASS (zero sorry)
  - Executables:  PASS (3 targets)
  - Phase 15:     PASS (data plane)
  - Phase 20:     PASS (core kernel)
  - Phase 25:     PASS (full kernel)
```

## Manual Verification

### Step 1: Environment Setup

```bash
# Install Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone repository
git clone https://github.com/Abraxas1010/lean-kernel-sky
cd lean-kernel-sky/RESEARCHER_BUNDLE

# Verify toolchain
cat lean-toolchain
# Should show: leanprover/lean4:v4.15.0
```

### Step 2: Sorry Check

```bash
# Must return nothing
grep -rn "sorry\|admit" HeytingLean --include="*.lean"
```

### Step 3: Library Build

```bash
lake build --wfail
```

The `--wfail` flag causes the build to fail on any warnings, ensuring strict compilation.

### Step 4: Executable Builds

```bash
lake build lean4lean_sky_demo
lake build kernel_sky_demo
lake build full_kernel_sky_demo
```

### Step 5: Cross-Validation

```bash
# Phase 15: Data plane
lake exe lean4lean_sky_demo --case expr
# Expected: [lean4lean_sky_demo] ok (case=expr)

# Phase 20: Core kernel (β/ζ)
lake exe kernel_sky_demo --case all
# Expected: [kernel_sky_demo] ok (case=all)

# Phase 25: Full kernel (β/ζ/δ/ι)
lake exe full_kernel_sky_demo --case all
# Expected: [full_kernel_sky_demo] ok (case=all)
```

## Reproducibility Hashes

Generate hashes for your build:

```bash
# Source hash
find HeytingLean -name "*.lean" -exec sha256sum {} \; | sort | sha256sum

# Executable hash
sha256sum .lake/build/bin/*_demo
```

Compare with published hashes to verify identical builds.

## Docker Verification

For isolated reproduction:

```dockerfile
FROM ghcr.io/leanprover/lean4:v4.15.0

WORKDIR /app
COPY RESEARCHER_BUNDLE .

RUN lake build --wfail
RUN lake build lean4lean_sky_demo kernel_sky_demo full_kernel_sky_demo
RUN lake exe full_kernel_sky_demo --case all
```

## CI/CD Integration

```yaml
# .github/workflows/verify.yml
name: Verify
on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with:
          toolchain: leanprover/lean4:v4.15.0
      - run: |
          cd RESEARCHER_BUNDLE
          ./scripts/verify_lean_kernel.sh
```

## Axiom Audit

The formalization uses only standard Lean kernel axioms:

```bash
lake env lean --run - <<EOF
import HeytingLean
#print axioms FullKernelSKY.whnfFullSky
EOF
```

Expected axioms:
- `propext` — Propositional extensionality
- `Classical.choice` — Axiom of choice
- `Quot.sound` — Quotient soundness

**No project-specific axioms.**

## Test Cases

### Data Plane Tests (Phase 15)

| Test | Description | Validates |
|------|-------------|-----------|
| `expr` | BVar/App/Lam encoding | Scott 9-ary |
| `ulevel` | Zero/Succ/Max encoding | Scott 6-ary |

### Core Kernel Tests (Phase 20)

| Test | Description | Validates |
|------|-------------|-----------|
| `whnf_id` | `(λx.x) 42 → 42` | β-reduction |
| `whnf_let` | `let x := 1 in x → 1` | ζ-reduction |
| `defeq_refl` | `e =?= e` | Structural equality |
| `infer_nat` | `infer(42) = Nat` | Type inference |

### Full Kernel Tests (Phase 25)

| Test | Description | Validates |
|------|-------------|-----------|
| `delta_unfold` | Constant unfolding | δ-reduction |
| `iota_nat` | `Nat.casesOn (succ n)` | ι-reduction |
| `full_whnf` | Combined reductions | β/ζ/δ/ι |

## Troubleshooting

### "lake: command not found"
Install elan: `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`

### "version mismatch"
Ensure toolchain matches: `cat lean-toolchain`

### "mathlib download failed"
Run: `lake update` then `lake build`

### "out of memory"
Increase stack: `ulimit -s unlimited`
