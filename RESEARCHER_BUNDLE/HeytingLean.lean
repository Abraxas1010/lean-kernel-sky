-- LoF Kernel: From Distinction to Type Theory
-- A verified pipeline from Laws of Form through SKY combinators to Lean's type checker

-- Layer 0: Laws of Form (Distinction)
import HeytingLean.LoF.Foundation.Blocks
import HeytingLean.LoF.Foundation.Soundness

-- Layer 1: Boolean Gates / Circuits
import HeytingLean.LoF.LoFPrimary.Syntax
import HeytingLean.LoF.LoFPrimary.Normalization
import HeytingLean.LoF.LoFPrimary.Rewrite
import HeytingLean.LoF.LoFPrimary.Optimize
import HeytingLean.LoF.LoFPrimary.AIG
import HeytingLean.LoF.LoFPrimary.GateSpec
import HeytingLean.LoF.LoFPrimary.MuxNet

-- Layer 2: Lambda Calculus
import HeytingLean.LoF.Combinators.STLC
import HeytingLean.LoF.Combinators.STLCSKY

-- Layer 3: SKY Combinators
import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.BracketAbstractionCorrectness
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.LoF.Combinators.GraphReduction

-- Layer 4: Eigenforms / Fixed Points
import HeytingLean.LoF.Combinators.EigenformBridge
import HeytingLean.LoF.Combinators.Denotational

-- Layer 5: Heyting Algebras / Nuclei
import HeytingLean.LoF.Combinators.Heyting.Nucleus
import HeytingLean.LoF.Combinators.Heyting.FixedPoints
import HeytingLean.LoF.Combinators.Heyting.FixedPointHeyting
import HeytingLean.LoF.Combinators.Heyting.Stability
import HeytingLean.LoF.Combinators.Heyting.Trichotomy
import HeytingLean.LoF.Combinators.Heyting.CombinatorMap
import HeytingLean.LoF.Combinators.Heyting.NucleusRangeOps

-- Layer 6: Category / Topos
import HeytingLean.LoF.Combinators.Category.MultiwayCategory
import HeytingLean.LoF.Combinators.Category.BranchialCategory
import HeytingLean.LoF.Combinators.Category.Groupoid
import HeytingLean.LoF.Combinators.Topos.SieveFrame
import HeytingLean.LoF.Combinators.Topos.SieveNucleus
import HeytingLean.LoF.Combinators.Topos.StepsSite
import HeytingLean.LoF.Combinators.Rewriting.CriticalPairs
import HeytingLean.LoF.Combinators.Rewriting.LocalConfluence
import HeytingLean.LoF.Combinators.Rewriting.LocalConfluenceBounded
import HeytingLean.LoF.Combinators.Rewriting.StepAt
import HeytingLean.LoF.Combinators.Rewriting.StepAtCompute

-- Layer 7: Lean Kernel (Data Plane - Phases 7-15)
import HeytingLean.LoF.LeanKernel.UniverseLevel
import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Inductive
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

-- Layer 7: Lean Kernel (Computation Plane - Phases 16-20)
import HeytingLean.LoF.LeanKernel.WHNFSKY
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.InferSKY
import HeytingLean.LoF.LeanKernel.KernelSKY

-- Layer 7: Lean Kernel (Full Kernel - Phases 21-25)
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.WHNFDeltaSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY

-- Tests
import HeytingLean.Tests.LeanKernelSanity
