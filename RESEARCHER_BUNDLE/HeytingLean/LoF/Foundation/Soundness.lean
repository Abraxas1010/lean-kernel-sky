import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Merkle
import HeytingLean.LoF.Foundation.Blocks

/-!
Formal integration layer (lightweight):
Bridges KernelRule to a simple RuleSpec and shows that all rules included in
the minted CAB (Beta, DeltaNatAdd) are admissible under the LoF witness bundle.

Note: This module intentionally keeps the logical predicate abstract to avoid
heavy dependencies, yet demonstrates that Lean itself can certify that every
KernelRule carried by the CAB has a corresponding LoF-backed witness.
-/

namespace HeytingLean
namespace LoF
namespace Foundation

open HeytingLean.Meta.LeanTT0

inductive RuleSpec where
  | BetaLamAppSpec
  | DeltaPrimNatAddSpec
  deriving Inhabited, BEq

def specOfRule : KernelRule → RuleSpec
  | .BetaLamApp      => .BetaLamAppSpec
  | .DeltaPrimNatAdd => .DeltaPrimNatAddSpec

def ruleSpecName : RuleSpec → String
  | .BetaLamAppSpec => "BetaLamApp"
  | .DeltaPrimNatAddSpec => "DeltaPrimNatAdd"

/-- Nontrivial predicate (as data): “this CAB rule is backed by a named LoF block in the bundle.” -/
def Provable_LoF (s : RuleSpec) : Type :=
  { b : HeytingLean.LoF.Foundation.Block //
      b.spec.name = ruleSpecName s ∧ b ∈ HeytingLean.LoF.Foundation.witnessBundle }

theorem beta_from_lof : Provable_LoF RuleSpec.BetaLamAppSpec := by
  refine ⟨HeytingLean.LoF.Foundation.betaLamAppBlock, ?_, ?_⟩
  · rfl
  · simp [HeytingLean.LoF.Foundation.witnessBundle]

theorem delta_from_lof : Provable_LoF RuleSpec.DeltaPrimNatAddSpec := by
  refine ⟨HeytingLean.LoF.Foundation.deltaPrimNatAddBlock, ?_, ?_⟩
  · rfl
  · simp [HeytingLean.LoF.Foundation.witnessBundle]

def Admissible (r : KernelRule) : Type := Provable_LoF (specOfRule r)

theorem admissible_beta : Admissible .BetaLamApp := beta_from_lof
theorem admissible_delta : Admissible .DeltaPrimNatAdd := delta_from_lof

/-- The CAB minted in this repository enumerates exactly these rules. -/
def cabRules : List KernelRule := [.BetaLamApp, .DeltaPrimNatAdd]

theorem admissible_all (r : KernelRule) (h : r ∈ cabRules) : Admissible r := by
  cases r <;> (cases h <;> first | exact admissible_beta | exact admissible_delta)

/-- The Merkle root over CAB rules (Lean-side) used for membership proofs. -/
def cabRulesRoot : ByteArray :=
  merkleRoot (cabRules.map (fun r => (ruleId r).hash))

end Foundation
end LoF
end HeytingLean
