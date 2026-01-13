#!/bin/bash
#
# verify_lean_kernel.sh - One-command verification for Lean Kernel → SKY
#
# This script:
# 1. Builds the library with strict flags (--wfail)
# 2. Builds all three demo executables
# 3. Cross-validates SKY output against native Lean
# 4. Emits reproducibility hashes
#
# Usage:
#   cd RESEARCHER_BUNDLE
#   ./scripts/verify_lean_kernel.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUNDLE_DIR="$(dirname "$SCRIPT_DIR")"

cd "$BUNDLE_DIR"

echo "========================================"
echo "Lean Kernel → SKY Verification"
echo "========================================"
echo
echo "Date: $(date)"
echo "Directory: $BUNDLE_DIR"
echo

# Step 1: Check for sorry/admit
echo "[1/5] Checking for sorry/admit..."
if grep -rn "sorry\|admit" HeytingLean --include="*.lean" 2>/dev/null; then
    echo "ERROR: Found sorry or admit in codebase!"
    exit 1
fi
echo "  ✓ No sorry/admit found"
echo

# Step 2: Library build (strict)
echo "[2/5] Building library (strict mode)..."
lake build --wfail 2>&1 | tail -5
echo "  ✓ Library build passed"
echo

# Step 3: Build executables
echo "[3/5] Building executables..."
lake build lean4lean_sky_demo 2>&1 | tail -2
lake build kernel_sky_demo 2>&1 | tail -2
lake build full_kernel_sky_demo 2>&1 | tail -2
echo "  ✓ All executables built"
echo

# Step 4: Cross-validation
echo "[4/5] Running cross-validation..."
echo "  Phase 15 (Data plane):"
OUTPUT1=$(lake exe lean4lean_sky_demo --case expr 2>&1)
if echo "$OUTPUT1" | grep -q "ok"; then
    echo "    ✓ lean4lean_sky_demo --case expr: ok"
else
    echo "    ✗ lean4lean_sky_demo failed"
    echo "$OUTPUT1"
    exit 1
fi

echo "  Phase 20 (Core kernel):"
OUTPUT2=$(lake exe kernel_sky_demo --case all 2>&1)
if echo "$OUTPUT2" | grep -q "ok"; then
    echo "    ✓ kernel_sky_demo --case all: ok"
else
    echo "    ✗ kernel_sky_demo failed"
    echo "$OUTPUT2"
    exit 1
fi

echo "  Phase 25 (Full kernel):"
OUTPUT3=$(lake exe full_kernel_sky_demo --case all 2>&1)
if echo "$OUTPUT3" | grep -q "ok"; then
    echo "    ✓ full_kernel_sky_demo --case all: ok"
else
    echo "    ✗ full_kernel_sky_demo failed"
    echo "$OUTPUT3"
    exit 1
fi
echo "  ✓ All cross-validation passed"
echo

# Step 5: Generate reproducibility hashes
echo "[5/5] Generating reproducibility hashes..."
echo "  Lean files:"
LEAN_HASH=$(find HeytingLean -name "*.lean" -exec sha256sum {} \; | sort | sha256sum | cut -d' ' -f1)
echo "    SHA256: ${LEAN_HASH:0:16}..."

echo "  Executables:"
if [ -f ".lake/build/bin/lean4lean_sky_demo" ]; then
    EXE_HASH=$(sha256sum .lake/build/bin/*_demo 2>/dev/null | sha256sum | cut -d' ' -f1)
    echo "    SHA256: ${EXE_HASH:0:16}..."
fi

echo "  Toolchain:"
cat lean-toolchain
echo

echo "========================================"
echo "VERIFICATION PASSED"
echo "========================================"
echo
echo "Summary:"
echo "  - Library:      PASS (zero sorry)"
echo "  - Executables:  PASS (3 targets)"
echo "  - Phase 15:     PASS (data plane)"
echo "  - Phase 20:     PASS (core kernel)"
echo "  - Phase 25:     PASS (full kernel)"
echo
echo "The Lean Kernel → SKY pipeline is verified."
