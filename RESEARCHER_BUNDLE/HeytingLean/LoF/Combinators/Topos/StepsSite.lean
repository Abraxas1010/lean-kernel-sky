import HeytingLean.LoF.Combinators.SKY

import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace HeytingLean
namespace LoF

namespace Comb

/-- Append multi-step reductions. -/
theorem Steps.transitive {t u v : Comb} : Steps t u → Steps u v → Steps t v := by
  intro htu huv
  induction htu with
  | refl t =>
      simpa using huv
  | trans hstep hsteps ih =>
      exact Steps.trans hstep (ih huv)

end Comb

/-- The preorder on terms induced by reachability via `Comb.Steps`. -/
instance : Preorder Comb where
  le := Comb.Steps
  le_refl t := Comb.Steps.refl t
  le_trans _ _ _ hab hbc := Comb.Steps.transitive hab hbc

end LoF
end HeytingLean

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Topos

open CategoryTheory

/-- The thin category of SKY terms ordered by reachability (`Comb.Steps`). -/
abbrev StepsCat := HeytingLean.LoF.Comb

/-- The dense Grothendieck topology on the reachability category. -/
def stepsDenseTopology : GrothendieckTopology StepsCat :=
  GrothendieckTopology.dense

end Topos
end Combinators
end LoF
end HeytingLean

