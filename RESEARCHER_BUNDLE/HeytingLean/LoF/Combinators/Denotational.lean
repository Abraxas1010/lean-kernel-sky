import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Bauer.ScottReflexiveDomain

/-!
# Denotational semantics of SKY combinators (interface-first)

This module gives a typed denotational semantics for the minimal `SKY` rewrite system
(`HeytingLean.LoF.Combinators.SKY`) into an arbitrary carrier `α`.

We proceed *interface-first*:

* `SKYModel α` packages an application operation and interpretations of `S`, `K`, `Y`
  satisfying the expected equational laws.
* Under such a model, every one-step reduction is sound (`denote_step`) and therefore
  every multi-step reduction is sound (`denote_steps`).

To connect this to the repo’s Scott-domain layer, `ScottSKYModel α` specializes `SKYModel`
to the `ReflexiveDomain.app` operation from `HeytingLean.LoF.Bauer.ScottReflexiveDomain`.
This keeps the semantics *typed* (in an `ωCPO` with bottom) while remaining proof-light
and warning-free.

Note: Constructing concrete `S/K/Y` *from* a reflexive domain equivalence is a deeper
domain-theoretic task (it requires additional continuity structure on the equivalence).
The present file isolates the correctness obligation: once such constants are provided,
rewrite soundness is automatic.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

universe u

/-! ## Abstract SKY models -/

structure SKYModel (α : Type u) where
  app : α → α → α
  K : α
  S : α
  Y : α
  appK : ∀ x y : α, app (app K x) y = x
  appS : ∀ x y z : α, app (app (app S x) y) z = app (app x z) (app y z)
  appY : ∀ f : α, app Y f = app f (app Y f)

namespace SKYModel

variable {α : Type u}

def denote (M : SKYModel α) : Comb → α
  | .K => M.K
  | .S => M.S
  | .Y => M.Y
  | .app f a => M.app (denote M f) (denote M a)

@[simp] theorem denote_K (M : SKYModel α) : denote M .K = M.K := rfl
@[simp] theorem denote_S (M : SKYModel α) : denote M .S = M.S := rfl
@[simp] theorem denote_Y (M : SKYModel α) : denote M .Y = M.Y := rfl
@[simp] theorem denote_app (M : SKYModel α) (f a : Comb) :
    denote M (.app f a) = M.app (denote M f) (denote M a) := rfl

theorem denote_step (M : SKYModel α) {t u : Comb} (h : Comb.Step t u) :
    denote M t = denote M u := by
  induction h with
  | K_rule x y =>
      simp [denote]
      exact M.appK (denote M x) (denote M y)
  | S_rule x y z =>
      simp [denote]
      exact M.appS (denote M x) (denote M y) (denote M z)
  | Y_rule f =>
      simp [denote]
      exact M.appY (denote M f)
  | app_left _ ih =>
      simp [denote, ih]
  | app_right _ ih =>
      simp [denote, ih]

theorem denote_steps (M : SKYModel α) {t u : Comb} (h : Comb.Steps t u) :
    denote M t = denote M u := by
  induction h with
  | refl t => rfl
  | trans hstep _ ih =>
      exact (denote_step M hstep).trans ih

end SKYModel

/-! ## Scott-domain specialization -/

open HeytingLean.LoF.Bauer

structure ScottSKYModel (α : Type u) [OmegaCompletePartialOrder α] [OrderBot α] where
  D : ReflexiveDomain (α := α)
  K : α
  S : α
  Y : α
  appK : ∀ x y : α, D.app (D.app K x) y = x
  appS : ∀ x y z : α, D.app (D.app (D.app S x) y) z = D.app (D.app x z) (D.app y z)
  appY : ∀ f : α, D.app Y f = D.app f (D.app Y f)

namespace ScottSKYModel

variable {α : Type u} [OmegaCompletePartialOrder α] [OrderBot α]

def toSKYModel (M : ScottSKYModel α) : SKYModel α where
  app := fun f x => M.D.app f x
  K := M.K
  S := M.S
  Y := M.Y
  appK := M.appK
  appS := M.appS
  appY := M.appY

theorem denote_steps_sound (M : ScottSKYModel α) {t u : Comb} (h : Comb.Steps t u) :
    SKYModel.denote (M.toSKYModel) t = SKYModel.denote (M.toSKYModel) u :=
  SKYModel.denote_steps (M := M.toSKYModel) h

end ScottSKYModel

end Combinators
end LoF
end HeytingLean
