import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.LoF.Combinators.Heyting.Trichotomy
import HeytingLean.LoF.Combinators.Heyting.FixedPointHeyting
import HeytingLean.LoF.Combinators.Topos.SieveNucleus
import HeytingLean.LoF.Combinators.Topos.ClosedSievesHeyting

/-!
Axioms audit for the SKY slice.

This file can be executed via:

`lake env lean HeytingLean/LoF/Combinators/AxiomsAudit.lean`

It prints the kernel footprint (`#print axioms`) of the headline results.
-/

-- SKY core
#print axioms HeytingLean.LoF.Comb.I_reduces

-- Labeled step enumerator
#print axioms HeytingLean.LoF.Comb.rootStep?_sound
#print axioms HeytingLean.LoF.Comb.stepEdgesList_sound
#print axioms HeytingLean.LoF.Comb.stepEdges_sound
#print axioms HeytingLean.LoF.Comb.stepEdgesList_complete
#print axioms HeytingLean.LoF.Comb.stepEdges_complete

-- Heyting extension (nucleus fixed points + instability witnesses)
#print axioms HeytingLean.LoF.Combinators.Heyting.heyting_trichotomy
#print axioms HeytingLean.LoF.Combinators.Heyting.no_fixedPointOperator_bool
#print axioms HeytingLean.LoF.Combinators.Heyting.fixedPoints_eq_range

-- Topos/sheaf layer (sieve closure as a nucleus; gluing via closed sieves)
#print axioms HeytingLean.LoF.Combinators.Topos.close_inf
#print axioms HeytingLean.LoF.Combinators.Topos.sieveNucleus
#print axioms HeytingLean.LoF.Combinators.Topos.mem_fixedPoints_sieveNucleus_iff_isClosed
#print axioms HeytingLean.LoF.Combinators.Topos.closedSieves_isSheaf
#print axioms HeytingLean.LoF.Combinators.Topos.closedSieve_instHeyting
#print axioms HeytingLean.LoF.Combinators.Topos.closedSieveEquivIsClosed

