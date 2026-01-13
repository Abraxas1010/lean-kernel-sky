/-!
# LoF.Foundation.Blocks — LoF "witness bundle" façade (v0)

This module is intentionally lightweight: it provides a concrete, explicit bundle of "blocks"
associated to kernel rules, with a stable digest per block. The `Soundness` integration layer uses
this bundle to avoid placeholder `True` predicates when linking CAB/TT0 rules to LoF artifacts.

This is *not yet* a full proof-producing LoF derivation of kernel rules; it is the minimal,
nontrivial bridge needed so rule admissibility is backed by explicit, named artifacts.
-/

namespace HeytingLean
namespace LoF
namespace Foundation

structure BlockSpec where
  name : String
  spec : String
  deriving Repr, Inhabited

structure Witness where
  digest : ByteArray

structure Block where
  spec : BlockSpec
  witness : Witness

def mkStub (name spec : String) : Block :=
  let bs := (name ++ ":" ++ spec).toUTF8
  { spec := { name, spec }, witness := { digest := bs } }

def betaLamAppBlock : Block :=
  mkStub "BetaLamApp" "((λx. b) a) ⇒ b[x:=a]"

def deltaPrimNatAddBlock : Block :=
  mkStub "DeltaPrimNatAdd" "Nat.add: (m + n) reduces to a numeral"

/-- The explicit LoF witness bundle used by the CAB/TT0 soundness bridge. -/
def witnessBundle : List Block :=
  [betaLamAppBlock, deltaPrimNatAddBlock]

end Foundation
end LoF
end HeytingLean
