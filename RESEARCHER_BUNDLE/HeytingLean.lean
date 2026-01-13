-- Lean Kernel → SKY Combinators
-- A verified pipeline for compiling Lean's type checker to minimal combinators

import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded

import HeytingLean.LoF.LeanKernel.UniverseLevel
import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Inductive
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.WHNFSKY
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.InferSKY
import HeytingLean.LoF.LeanKernel.KernelSKY
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.WHNFDeltaSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY

import HeytingLean.Tests.LeanKernelSanity
