import HeytingLean.LoF.Combinators.Heyting.Nucleus
import HeytingLean.LoF.Combinators.Topos.StepsSite

import Mathlib.CategoryTheory.Sites.Closed

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory
open Order
open HeytingLean.LoF.Combinators.Heyting

universe v u

variable {C : Type u} [Category.{v} C]

/-- The closure operation of a Grothendieck topology preserves finite meets of sieves. -/
theorem close_inf (J : GrothendieckTopology C) {X : C} (S T : Sieve X) :
    J.close (S ⊓ T) = J.close S ⊓ J.close T := by
  ext Y f
  change J.Covers (S ⊓ T) f ↔ (J.Covers S f ∧ J.Covers T f)
  change (S ⊓ T).pullback f ∈ J Y ↔ (S.pullback f ∈ J Y ∧ T.pullback f ∈ J Y)
  simp [Sieve.pullback_inter]

/-- Any Grothendieck topology gives a nucleus on sieves via `J.close`. -/
def sieveNucleus (J : GrothendieckTopology C) (X : C) : Nucleus (Sieve X) where
  toInfHom :=
    { toFun := J.close
      map_inf' := by
        intro S T
        simpa using close_inf (J := J) (S := S) (T := T) }
  idempotent' := by
    intro S
    simp [J.close_close S]
  le_apply' := by
    intro S
    exact J.le_close S

/-- Fixed points of the sieve nucleus are exactly the `J`-closed sieves. -/
theorem mem_fixedPoints_sieveNucleus_iff_isClosed (J : GrothendieckTopology C) {X : C}
    (S : Sieve X) : (S ∈ Ω_ (sieveNucleus (C := C) J X)) ↔ J.IsClosed S := by
  change (J.close S = S) ↔ J.IsClosed S
  simpa using (J.isClosed_iff_close_eq_self S).symm

/-- The presheaf of closed sieves is a sheaf for any Grothendieck topology. -/
theorem closedSieves_isSheaf (J : GrothendieckTopology C) :
    Presieve.IsSheaf J (Functor.closedSieves J) :=
  CategoryTheory.classifier_isSheaf (J₁ := J)

/-- The sieve nucleus associated to the dense topology on the SKY reachability site. -/
abbrev stepsSieveNucleus (X : StepsCat) : Nucleus (Sieve X) :=
  sieveNucleus (C := StepsCat) (J := stepsDenseTopology) X

end Topos
end Combinators
end LoF
end HeytingLean

