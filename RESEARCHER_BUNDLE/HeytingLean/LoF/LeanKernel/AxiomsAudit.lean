import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.FullKernelSKY

/-!
Axioms audit for the LeanKernel slice.

This file is intended to be *run directly* (not imported):

`lake env lean HeytingLean/LoF/LeanKernel/AxiomsAudit.lean`

It prints the kernel footprint (`#print axioms`) of the headline kernel
definitions and their computation-plane encodings.
-/

-- Native (reference) kernel algorithms
#print axioms HeytingLean.LoF.LeanKernel.WHNF.whnfWithDelta
#print axioms HeytingLean.LoF.LeanKernel.DefEq.isDefEqWithDelta
#print axioms HeytingLean.LoF.LeanKernel.Infer.infer?
#print axioms HeytingLean.LoF.LeanKernel.Infer.check

-- Computation-plane kernel programs (λ terms compiled to SKY)
#print axioms HeytingLean.LoF.LeanKernel.FullKernelSKY.whnfFullSky
#print axioms HeytingLean.LoF.LeanKernel.FullKernelSKY.isDefEqFullSky
#print axioms HeytingLean.LoF.LeanKernel.FullKernelSKY.inferFullSky
#print axioms HeytingLean.LoF.LeanKernel.FullKernelSKY.checkFullSky

