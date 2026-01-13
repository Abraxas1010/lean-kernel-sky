import HeytingLean.LoF.Combinators.SKY

/-!
# GraphReduction — a heap-style SKY reducer (Phase 1 scaffold)

This file introduces a *graph / heap* representation for SKY terms together with a rooted
small-step reduction relation that:

* rewrites at the graph root (no contextual closure yet),
* allocates fresh `app` nodes for `S`/`Y` unfolding (sharing-friendly),
* and is *sound* w.r.t. the existing term-level `Comb.Step`.

The goal is to make later “hardware-targetable” machines (stack + heap) talk to the existing
SKY rewrite system without changing `Comb`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace SKYGraph

abbrev NodeId := Nat

inductive Node (OracleRef : Type) where
  | combK
  | combS
  | combY
  | app (f a : NodeId)
  | oracle (ref : OracleRef)
deriving Repr

structure Graph (OracleRef : Type) where
  nodes : Array (Node OracleRef)
  root : NodeId
deriving Repr

namespace Graph

variable {OracleRef : Type}

abbrev node? (g : Graph OracleRef) (i : NodeId) : Option (Node OracleRef) :=
  g.nodes[i]?

theorem lt_nodes_size_of_node?_eq_some (g : Graph OracleRef) {i : NodeId} {n : Node OracleRef}
    (h : g.node? i = some n) : i < g.nodes.size := by
  classical
  unfold node? at h
  by_cases hi : i < g.nodes.size
  · exact hi
  · simp [hi] at h

def pushNode (g : Graph OracleRef) (n : Node OracleRef) : Graph OracleRef × NodeId :=
  let id := g.nodes.size
  ({ g with nodes := g.nodes.push n }, id)

structure NodesPrefix (nodes nodes' : Array (Node OracleRef)) : Prop where
  size_le : nodes.size ≤ nodes'.size
  idx_eq : ∀ i, i < nodes.size → nodes'[i]? = nodes[i]?

theorem NodesPrefix.refl (nodes : Array (Node OracleRef)) : NodesPrefix nodes nodes :=
  { size_le := Nat.le_refl _, idx_eq := by intro i hi; rfl }

theorem NodesPrefix.trans {a b c : Array (Node OracleRef)} :
    NodesPrefix a b → NodesPrefix b c → NodesPrefix a c := by
  intro hab hbc
  refine ⟨Nat.le_trans hab.size_le hbc.size_le, ?_⟩
  intro i hi
  have hi' : i < b.size := Nat.lt_of_lt_of_le hi hab.size_le
  exact (hbc.idx_eq i hi').trans (hab.idx_eq i hi)

theorem NodesPrefix.push (nodes : Array (Node OracleRef)) (n : Node OracleRef) :
    NodesPrefix nodes (nodes.push n) := by
  classical
  refine ⟨by simp, ?_⟩
  intro i hi
  have hne : i ≠ nodes.size := Nat.ne_of_lt hi
  -- `i < nodes.size` implies we are in the "old prefix" branch.
  simp [Array.getElem?_push, hne]

end Graph

/-! ## Relating heaps back to term syntax -/

inductive Realizes {OracleRef : Type} (oracle : OracleRef → Comb) (g : Graph OracleRef) :
    NodeId → Comb → Prop where
  | K {i : NodeId} (h : g.node? i = some (Node.combK (OracleRef := OracleRef))) :
      Realizes oracle g i .K
  | S {i : NodeId} (h : g.node? i = some (Node.combS (OracleRef := OracleRef))) :
      Realizes oracle g i .S
  | Y {i : NodeId} (h : g.node? i = some (Node.combY (OracleRef := OracleRef))) :
      Realizes oracle g i .Y
  | app {i f a : NodeId} {tf ta : Comb}
      (h : g.node? i = some (Node.app (OracleRef := OracleRef) f a))
      (hf : Realizes oracle g f tf) (ha : Realizes oracle g a ta) :
      Realizes oracle g i (.app tf ta)
  | oracle {i : NodeId} (ref : OracleRef)
      (h : g.node? i = some (Node.oracle (OracleRef := OracleRef) ref)) :
      Realizes oracle g i (oracle ref)

namespace Realizes

open Graph

variable {OracleRef : Type} {oracle : OracleRef → Comb}

theorem weaken {g : Graph OracleRef} {g' : Graph OracleRef}
    (hp : Graph.NodesPrefix (OracleRef := OracleRef) g.nodes g'.nodes)
    {i : NodeId} {t : Comb} :
    Realizes oracle g i t → Realizes oracle g' i t := by
  intro h
  induction h with
  | K h =>
      rename_i i
      refine Realizes.K (oracle := oracle) (g := g') (i := i) ?_
      have hi : i < g.nodes.size := Graph.lt_nodes_size_of_node?_eq_some (g := g) h
      have := hp.idx_eq i hi
      simpa [Graph.node?] using this.trans h
  | S h =>
      rename_i i
      refine Realizes.S (oracle := oracle) (g := g') (i := i) ?_
      have hi : i < g.nodes.size := Graph.lt_nodes_size_of_node?_eq_some (g := g) h
      have := hp.idx_eq i hi
      simpa [Graph.node?] using this.trans h
  | Y h =>
      rename_i i
      refine Realizes.Y (oracle := oracle) (g := g') (i := i) ?_
      have hi : i < g.nodes.size := Graph.lt_nodes_size_of_node?_eq_some (g := g) h
      have := hp.idx_eq i hi
      simpa [Graph.node?] using this.trans h
  | app hnode _ _ ihf iha =>
      have hi : _ < g.nodes.size := Graph.lt_nodes_size_of_node?_eq_some (g := g) hnode
      have hx := hp.idx_eq _ hi
      refine Realizes.app (oracle := oracle) (g := g') ?_ ihf iha
      simpa [Graph.node?] using hx.trans hnode
  | oracle ref hnode =>
      rename_i i
      refine Realizes.oracle (oracle := oracle) (g := g') (i := i) ref ?_
      have hi : i < g.nodes.size := Graph.lt_nodes_size_of_node?_eq_some (g := g) hnode
      have := hp.idx_eq i hi
      simpa [Graph.node?] using this.trans hnode

end Realizes

/-! ## Rooted graph reduction rules -/

namespace Graph

variable {OracleRef : Type}

def stepS (g : Graph OracleRef) (xId yId zId : NodeId) : Graph OracleRef :=
  let (g1, xz) := g.pushNode (.app xId zId)
  let (g2, yz) := g1.pushNode (.app yId zId)
  let (g3, out) := g2.pushNode (.app xz yz)
  { g3 with root := out }

def stepY (g : Graph OracleRef) (yId fId : NodeId) : Graph OracleRef :=
  let (g1, self) := g.pushNode (.app yId fId)
  let (g2, out) := g1.pushNode (.app fId self)
  { g2 with root := out }

theorem root_stepS (g : Graph OracleRef) (xId yId zId : NodeId) :
    (stepS g xId yId zId).root = Nat.succ (Nat.succ g.nodes.size) := by
  classical
  unfold stepS Graph.pushNode
  simp

theorem root_stepY (g : Graph OracleRef) (yId fId : NodeId) :
    (stepY g yId fId).root = Nat.succ g.nodes.size := by
  classical
  unfold stepY Graph.pushNode
  simp

theorem nodesPrefix_stepS (g : Graph OracleRef) (xId yId zId : NodeId) :
    NodesPrefix (OracleRef := OracleRef) g.nodes (stepS g xId yId zId).nodes := by
  classical
  unfold stepS
  simp [Graph.pushNode]
  refine NodesPrefix.trans (NodesPrefix.push (OracleRef := OracleRef) g.nodes (.app xId zId)) ?_
  refine NodesPrefix.trans (NodesPrefix.push (OracleRef := OracleRef) (g.nodes.push (.app xId zId)) (.app yId zId)) ?_
  simpa using
    NodesPrefix.push (OracleRef := OracleRef) ((g.nodes.push (.app xId zId)).push (.app yId zId))
      (.app g.nodes.size (Nat.succ g.nodes.size))

theorem nodesPrefix_stepY (g : Graph OracleRef) (yId fId : NodeId) :
    NodesPrefix (OracleRef := OracleRef) g.nodes (stepY g yId fId).nodes := by
  classical
  unfold stepY
  simp [Graph.pushNode]
  refine NodesPrefix.trans (NodesPrefix.push (OracleRef := OracleRef) g.nodes (.app yId fId)) ?_
  simpa using NodesPrefix.push (OracleRef := OracleRef) (g.nodes.push (.app yId fId)) (.app fId g.nodes.size)

theorem node?_stepS_xz (g : Graph OracleRef) (xId yId zId : NodeId) :
    (stepS g xId yId zId).node? g.nodes.size = some (.app xId zId) := by
  classical
  simp only [Graph.node?, stepS, Graph.pushNode]
  have hp1 :
      NodesPrefix (OracleRef := OracleRef)
        (g.nodes.push (.app xId zId))
        ((g.nodes.push (.app xId zId)).push (.app yId zId)) :=
    NodesPrefix.push (OracleRef := OracleRef) (g.nodes.push (.app xId zId)) (.app yId zId)
  have hp2 :
      NodesPrefix (OracleRef := OracleRef)
        ((g.nodes.push (.app xId zId)).push (.app yId zId))
        (((g.nodes.push (.app xId zId)).push (.app yId zId)).push
          (.app g.nodes.size (g.nodes.push (.app xId zId)).size)) :=
    NodesPrefix.push (OracleRef := OracleRef) ((g.nodes.push (.app xId zId)).push (.app yId zId))
      (.app g.nodes.size (g.nodes.push (.app xId zId)).size)
  have hp :
      NodesPrefix (OracleRef := OracleRef)
        (g.nodes.push (.app xId zId))
        (((g.nodes.push (.app xId zId)).push (.app yId zId)).push
          (.app g.nodes.size (g.nodes.push (.app xId zId)).size)) :=
    NodesPrefix.trans hp1 hp2
  have hi : g.nodes.size < (g.nodes.push (.app xId zId)).size := by
    simp [Array.size_push]
  have hx := hp.idx_eq g.nodes.size hi
  simpa [Array.getElem?_push_size] using hx

theorem node?_stepS_yz (g : Graph OracleRef) (xId yId zId : NodeId) :
    (stepS g xId yId zId).node? (Nat.succ g.nodes.size) = some (.app yId zId) := by
  classical
  simp only [Graph.node?, stepS, Graph.pushNode]
  have hp :
      NodesPrefix (OracleRef := OracleRef)
        ((g.nodes.push (.app xId zId)).push (.app yId zId))
        (((g.nodes.push (.app xId zId)).push (.app yId zId)).push
          (.app g.nodes.size (g.nodes.push (.app xId zId)).size)) :=
    NodesPrefix.push (OracleRef := OracleRef) ((g.nodes.push (.app xId zId)).push (.app yId zId))
      (.app g.nodes.size (g.nodes.push (.app xId zId)).size)
  have hi : Nat.succ g.nodes.size < ((g.nodes.push (.app xId zId)).push (.app yId zId)).size := by
    simp [Array.size_push, Nat.succ_eq_add_one, Nat.add_assoc]
  have hx := hp.idx_eq (Nat.succ g.nodes.size) hi
  have hb :
      ((g.nodes.push (.app xId zId)).push (.app yId zId))[Nat.succ g.nodes.size]? =
        some (.app yId zId) := by
    simpa [Array.size_push, Nat.succ_eq_add_one] using
      (Array.getElem?_push_size (xs := g.nodes.push (.app xId zId)) (x := (.app yId zId)))
  exact hx.trans hb

theorem node?_stepS_out (g : Graph OracleRef) (xId yId zId : NodeId) :
    (stepS g xId yId zId).node? (Nat.succ (Nat.succ g.nodes.size))
      =
    some (.app g.nodes.size (Nat.succ g.nodes.size)) := by
  classical
  simp only [Graph.node?, stepS, Graph.pushNode]
  -- The third push adds exactly the `(xz, yz)` node at index `prefix.size = n+2`.
  simpa [Array.size_push, Nat.succ_eq_add_one, Nat.add_assoc] using
    (Array.getElem?_push_size
      (xs := (g.nodes.push (.app xId zId)).push (.app yId zId))
      (x := (.app g.nodes.size (g.nodes.push (.app xId zId)).size)))

theorem node?_stepY_self (g : Graph OracleRef) (yId fId : NodeId) :
    (stepY g yId fId).node? g.nodes.size = some (.app yId fId) := by
  classical
  simp only [Graph.node?, stepY, Graph.pushNode]
  have hp :
      NodesPrefix (OracleRef := OracleRef)
        (g.nodes.push (.app yId fId))
        ((g.nodes.push (.app yId fId)).push (.app fId g.nodes.size)) :=
    NodesPrefix.push (OracleRef := OracleRef) (g.nodes.push (.app yId fId)) (.app fId g.nodes.size)
  have hi : g.nodes.size < (g.nodes.push (.app yId fId)).size := by
    simp [Array.size_push]
  have hx := hp.idx_eq g.nodes.size hi
  simpa [Array.getElem?_push_size] using hx

theorem node?_stepY_out (g : Graph OracleRef) (yId fId : NodeId) :
    (stepY g yId fId).node? (Nat.succ g.nodes.size) = some (.app fId g.nodes.size) := by
  classical
  simp only [Graph.node?, stepY, Graph.pushNode]
  simpa [Array.size_push, Nat.succ_eq_add_one] using
    (Array.getElem?_push_size (xs := g.nodes.push (.app yId fId)) (x := (.app fId g.nodes.size)))

inductive Step (g g' : Graph OracleRef) : Prop where
  | K_rule {rootL rootR leftL leftR : NodeId}
      (hRoot : g.node? g.root = some (.app rootL rootR))
      (hL : g.node? rootL = some (.app leftL leftR))
      (hK : g.node? leftL = some .combK)
      (hNew : g' = { g with root := leftR }) :
      Step g g'
  | S_rule {rootL rootR aL aR sId xId yId zId : NodeId}
      (hRoot : g.node? g.root = some (.app rootL rootR))
      (hA : g.node? rootL = some (.app aL aR))
      (hB : g.node? aL = some (.app sId xId))
      (hS : g.node? sId = some .combS)
      (hIds : aR = yId ∧ rootR = zId)
      (hNew : g' = stepS g xId yId zId) :
      Step g g'
  | Y_rule {rootL rootR yId fId : NodeId}
      (hRoot : g.node? g.root = some (.app rootL rootR))
      (hY : g.node? rootL = some .combY)
      (hIds : rootL = yId ∧ rootR = fId)
      (hNew : g' = stepY g yId fId) :
      Step g g'

/-! ## Phase 3 hook: boolean oracle selection at the root -/

inductive StepOracle (oracleEval : OracleRef → Bool) (g g' : Graph OracleRef) : Prop where
  | base (h : Step g g') : StepOracle oracleEval g g'
  /--
  Oracle-driven boolean selection:

  If the root is `((oracle ref) x) y`, then rewrite the root pointer to `x` or `y`
  depending on `oracleEval ref`.

  This is a *rooted* rule (no contextual closure), intended to model “fast” boolean
  decisions (e.g. via an AIG pipeline) while recursion/application stays in SKY.
  -/
  | oracle_select {rootL rootR leftL leftR : NodeId} {ref : OracleRef}
      (hRoot : g.node? g.root = some (.app rootL rootR))
      (hL : g.node? rootL = some (.app leftL leftR))
      (hO : g.node? leftL = some (.oracle ref))
      (hNew : g' = { g with root := if oracleEval ref then leftR else rootR }) :
      StepOracle oracleEval g g'

/-! ## Soundness w.r.t. term-level rewriting -/

open Comb

variable {oracle : OracleRef → Comb}

theorem step_sound {g g' : Graph OracleRef} {t : Comb} (hstep : Step g g')
    (hreal : Realizes oracle g g.root t) :
    ∃ t', Comb.Step t t' ∧ Realizes oracle g' g'.root t' := by
  classical
  cases hstep with
  | K_rule hRoot hL hK hNew =>
      rename_i rootL rootR leftL leftR
      subst hNew
      cases hreal with
      | app hRoot' hRootL hRootR =>
          rename_i rootLId rootRId tRootL ty
          have hRoot'' : g.node? g.root = some (Node.app rootLId rootRId) := by
            simpa using hRoot'
          have hEq :
              some (Node.app (OracleRef := OracleRef) rootLId rootRId) =
                some (Node.app (OracleRef := OracleRef) rootL rootR) :=
            hRoot''.symm.trans hRoot
          have hNodeEq :
              Node.app (OracleRef := OracleRef) rootLId rootRId =
                Node.app (OracleRef := OracleRef) rootL rootR :=
            Option.some.inj hEq
          injection hNodeEq with hRootLId hRootRId
          subst rootLId
          subst rootRId
          cases hRootL with
          | app hL' hLeftL hLeftR =>
              rename_i leftLId leftRId tLeftL tx
              have hL'' : g.node? rootL = some (Node.app leftLId leftRId) := by
                simpa using hL'
              have hEq2 :
                  some (Node.app (OracleRef := OracleRef) leftLId leftRId) =
                    some (Node.app (OracleRef := OracleRef) leftL leftR) :=
                hL''.symm.trans hL
              have hNodeEq2 :
                  Node.app (OracleRef := OracleRef) leftLId leftRId =
                    Node.app (OracleRef := OracleRef) leftL leftR :=
                Option.some.inj hEq2
              injection hNodeEq2 with hLeftLId hLeftRId
              subst leftLId
              subst leftRId
              cases hLeftL with
              | K hK' =>
                  have : some (Node.combK (OracleRef := OracleRef)) = some (Node.combK (OracleRef := OracleRef)) :=
                    hK'.symm.trans hK
                  cases this
                  refine ⟨tx, ?_, ?_⟩
                  · simpa using (Comb.Step.K_rule (x := tx) (y := ty))
                  · have hp : NodesPrefix (OracleRef := OracleRef) g.nodes ({ g with root := leftR }.nodes) := by
                      simpa using NodesPrefix.refl (OracleRef := OracleRef) g.nodes
                    -- `leftR` is the new root.
                    simpa using
                      (Realizes.weaken (oracle := oracle) (g := g) (g' := { g with root := leftR }) hp hLeftR)
              | S h =>
                  cases (Option.some.inj (h.symm.trans hK))
              | Y h =>
                  cases (Option.some.inj (h.symm.trans hK))
              | app h _ _ =>
                  cases (Option.some.inj (h.symm.trans hK))
              | oracle _ h =>
                  cases (Option.some.inj (h.symm.trans hK))
          | K h =>
              cases (Option.some.inj (h.symm.trans hL))
          | S h =>
              cases (Option.some.inj (h.symm.trans hL))
          | Y h =>
              cases (Option.some.inj (h.symm.trans hL))
          | oracle _ h =>
              cases (Option.some.inj (h.symm.trans hL))
      | K h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | S h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | Y h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | oracle _ h =>
          cases (Option.some.inj (h.symm.trans hRoot))
  | S_rule hRoot hA hB hS hIds hNew =>
      rename_i rootL rootR aL aR sId xId yId zId
      rcases hIds with ⟨hAR, hRR⟩
      subst aR
      subst rootR
      subst hNew
      cases hreal with
      | app hRoot' hRootL hZ =>
          rename_i rootL' zId' tRootL tz
          have hRoot'' : g.node? g.root = some (Node.app rootL' zId') := by
            simpa using hRoot'
          have hEq :
              some (Node.app (OracleRef := OracleRef) rootL' zId') =
                some (Node.app (OracleRef := OracleRef) rootL zId) :=
            hRoot''.symm.trans hRoot
          have hNodeEq :
              Node.app (OracleRef := OracleRef) rootL' zId' =
                Node.app (OracleRef := OracleRef) rootL zId :=
            Option.some.inj hEq
          injection hNodeEq with hRootLId hZId
          subst rootL'
          subst zId'
          cases hRootL with
          | app hA' hAL hY =>
              rename_i aL' yId' tAL ty
              have hA'' : g.node? rootL = some (Node.app aL' yId') := by
                simpa using hA'
              have hEq2 :
                  some (Node.app (OracleRef := OracleRef) aL' yId') =
                    some (Node.app (OracleRef := OracleRef) aL yId) :=
                hA''.symm.trans hA
              have hNodeEq2 :
                  Node.app (OracleRef := OracleRef) aL' yId' =
                    Node.app (OracleRef := OracleRef) aL yId :=
                Option.some.inj hEq2
              injection hNodeEq2 with hALId hYId
              subst aL'
              subst yId'
              cases hAL with
              | app hB' hSx hX =>
                  rename_i sId' xId' tSx tx
                  have hB'' : g.node? aL = some (Node.app sId' xId') := by
                    simpa using hB'
                  have hEq3 :
                      some (Node.app (OracleRef := OracleRef) sId' xId') =
                        some (Node.app (OracleRef := OracleRef) sId xId) :=
                    hB''.symm.trans hB
                  have hNodeEq3 :
                      Node.app (OracleRef := OracleRef) sId' xId' =
                        Node.app (OracleRef := OracleRef) sId xId :=
                    Option.some.inj hEq3
                  injection hNodeEq3 with hSid' hXid'
                  subst sId'
                  subst xId'
                  cases hSx with
                  | S hS' =>
                      have : some (Node.combS (OracleRef := OracleRef)) = some (Node.combS (OracleRef := OracleRef)) :=
                        hS'.symm.trans hS
                      cases this
                      let gS : Graph OracleRef := stepS g xId yId zId
                      have hp : NodesPrefix (OracleRef := OracleRef) g.nodes gS.nodes :=
                        nodesPrefix_stepS (g := g) (xId := xId) (yId := yId) (zId := zId)
                      have hX' : Realizes oracle gS xId tx :=
                        Realizes.weaken (oracle := oracle) (g := g) (g' := gS) hp hX
                      have hY' : Realizes oracle gS yId ty :=
                        Realizes.weaken (oracle := oracle) (g := g) (g' := gS) hp hY
                      have hZ' : Realizes oracle gS zId tz :=
                        Realizes.weaken (oracle := oracle) (g := g) (g' := gS) hp hZ
                      let xz : NodeId := g.nodes.size
                      let yz : NodeId := Nat.succ g.nodes.size
                      let out : NodeId := Nat.succ (Nat.succ g.nodes.size)
                      have hXZnode : gS.node? xz = some (.app xId zId) := by
                        simpa [gS, xz] using node?_stepS_xz (g := g) (xId := xId) (yId := yId) (zId := zId)
                      have hYZnode : gS.node? yz = some (.app yId zId) := by
                        simpa [gS, yz] using node?_stepS_yz (g := g) (xId := xId) (yId := yId) (zId := zId)
                      have hOutNode : gS.node? out = some (.app xz yz) := by
                        have : gS.node? out = some (.app g.nodes.size (Nat.succ g.nodes.size)) := by
                          simpa [gS, out] using node?_stepS_out (g := g) (xId := xId) (yId := yId) (zId := zId)
                        simpa [xz, yz] using this
                      have hxz : Realizes oracle gS xz (.app tx tz) :=
                        Realizes.app (oracle := oracle) (g := gS) (i := xz) (f := xId) (a := zId)
                          (tf := tx) (ta := tz) hXZnode hX' hZ'
                      have hyz : Realizes oracle gS yz (.app ty tz) :=
                        Realizes.app (oracle := oracle) (g := gS) (i := yz) (f := yId) (a := zId)
                          (tf := ty) (ta := tz) hYZnode hY' hZ'
                      have hout : Realizes oracle gS out (.app (.app tx tz) (.app ty tz)) :=
                        Realizes.app (oracle := oracle) (g := gS) (i := out) (f := xz) (a := yz)
                          (tf := .app tx tz) (ta := .app ty tz) hOutNode hxz hyz
                      refine ⟨.app (.app tx tz) (.app ty tz), ?_, ?_⟩
                      · simpa using (Comb.Step.S_rule (x := tx) (y := ty) (z := tz))
                      · -- `out` is the root of `stepS`.
                        simpa [gS, root_stepS (g := g) (xId := xId) (yId := yId) (zId := zId), out] using hout
                  | K h =>
                      cases (Option.some.inj (h.symm.trans hS))
                  | Y h =>
                      cases (Option.some.inj (h.symm.trans hS))
                  | app h _ _ =>
                      cases (Option.some.inj (h.symm.trans hS))
                  | oracle _ h =>
                      cases (Option.some.inj (h.symm.trans hS))
              | K h =>
                  cases (Option.some.inj (h.symm.trans hB))
              | S h =>
                  cases (Option.some.inj (h.symm.trans hB))
              | Y h =>
                  cases (Option.some.inj (h.symm.trans hB))
              | oracle _ h =>
                  cases (Option.some.inj (h.symm.trans hB))
          | K h =>
              cases (Option.some.inj (h.symm.trans hA))
          | S h =>
              cases (Option.some.inj (h.symm.trans hA))
          | Y h =>
              cases (Option.some.inj (h.symm.trans hA))
          | oracle _ h =>
              cases (Option.some.inj (h.symm.trans hA))
      | K h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | S h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | Y h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | oracle _ h =>
          cases (Option.some.inj (h.symm.trans hRoot))
  | Y_rule hRoot hY hIds hNew =>
      rename_i rootL rootR yId fId
      rcases hIds with ⟨hL, hR⟩
      subst rootL
      subst rootR
      subst hNew
      cases hreal with
      | app hRoot' hYnode hF =>
          rename_i yId' fId' tY tF
          have hRoot'' : g.node? g.root = some (Node.app yId' fId') := by
            simpa using hRoot'
          have hEq :
              some (Node.app (OracleRef := OracleRef) yId' fId') =
                some (Node.app (OracleRef := OracleRef) yId fId) :=
            hRoot''.symm.trans hRoot
          have hNodeEq :
              Node.app (OracleRef := OracleRef) yId' fId' =
                Node.app (OracleRef := OracleRef) yId fId :=
            Option.some.inj hEq
          injection hNodeEq with hYid' hFid'
          subst yId'
          subst fId'
          cases hYnode with
          | Y hY' =>
              have : some (Node.combY (OracleRef := OracleRef)) = some (Node.combY (OracleRef := OracleRef)) :=
                hY'.symm.trans hY
              cases this
              let gY : Graph OracleRef := stepY g yId fId
              have hp : NodesPrefix (OracleRef := OracleRef) g.nodes gY.nodes :=
                nodesPrefix_stepY (g := g) (yId := yId) (fId := fId)
              have hY'node : Realizes oracle gY yId .Y :=
                Realizes.weaken (oracle := oracle) (g := g) (g' := gY) hp
                  (Realizes.Y (oracle := oracle) (g := g) (i := yId) hY')
              have hF' : Realizes oracle gY fId tF :=
                Realizes.weaken (oracle := oracle) (g := g) (g' := gY) hp hF
              let self : NodeId := g.nodes.size
              let out : NodeId := Nat.succ g.nodes.size
              have hSelfNode : gY.node? self = some (.app yId fId) := by
                simpa [gY, self] using node?_stepY_self (g := g) (yId := yId) (fId := fId)
              have hOutNode : gY.node? out = some (.app fId self) := by
                have : gY.node? out = some (.app fId g.nodes.size) := by
                  simpa [gY, out] using node?_stepY_out (g := g) (yId := yId) (fId := fId)
                simpa [self] using this
              have hSelf : Realizes oracle gY self (.app .Y tF) :=
                Realizes.app (oracle := oracle) (g := gY) (i := self) (f := yId) (a := fId)
                  (tf := .Y) (ta := tF) hSelfNode hY'node hF'
              have hOut : Realizes oracle gY out (.app tF (.app .Y tF)) :=
                Realizes.app (oracle := oracle) (g := gY) (i := out) (f := fId) (a := self)
                  (tf := tF) (ta := .app .Y tF) hOutNode hF' hSelf
              refine ⟨.app tF (.app .Y tF), ?_, ?_⟩
              · simpa using (Comb.Step.Y_rule (f := tF))
              · simpa [gY, root_stepY (g := g) (yId := yId) (fId := fId), out] using hOut
          | K h =>
              cases (Option.some.inj (h.symm.trans hY))
          | S h =>
              cases (Option.some.inj (h.symm.trans hY))
          | app h _ _ =>
              cases (Option.some.inj (h.symm.trans hY))
          | oracle _ h =>
              cases (Option.some.inj (h.symm.trans hY))
      | K h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | S h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | Y h =>
          cases (Option.some.inj (h.symm.trans hRoot))
      | oracle _ h =>
          cases (Option.some.inj (h.symm.trans hRoot))

end Graph

/-! ## Soundness (planned)

Next step (Phase 1 continuation): prove that `Graph.Step` is sound with respect to the
term-level `Comb.Step`, using `Realizes` to relate heap nodes back to SKY syntax.
-/

end SKYGraph
end Combinators
end LoF
end HeytingLean
