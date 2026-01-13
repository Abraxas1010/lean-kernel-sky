import HeytingLean.LoF.Combinators.GraphReduction

/-!
# SKYMachineBounded — bounded heap+stack abstract machine for SKY(+oracle)

This file provides a small deterministic abstract machine suitable as a *hardware spec*:

* heap: an `Array` of `SKYGraph.Node` (used prefix),
* focus: a node id,
* stack: pending argument node ids (spine stack),
* step: leftmost-outermost weak-head reduction (K/S/Y + oracle_select),
* resource bounds: compilation and runtime allocation are capped by `maxNodes`.

It is intended to support an FPGA demo by exporting:
1) an initial heap image,
2) an oracle circuit (AIGER), and
3) an expected output / trace computed by this reference model.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace SKYMachineBounded

open SKYGraph

structure State (OracleRef : Type) where
  nodes : Array (Node OracleRef)
  focus : NodeId
  stack : List NodeId
deriving Repr

namespace State

variable {OracleRef : Type}

def node? (s : State OracleRef) (i : NodeId) : Option (Node OracleRef) :=
  s.nodes[i]?

def pushNode (maxNodes : Nat) (s : State OracleRef) (n : Node OracleRef) : Option (State OracleRef × NodeId) :=
  if s.nodes.size < maxNodes then
    let id := s.nodes.size
    some ({ s with nodes := s.nodes.push n }, id)
  else
    none

private def compileAux (maxNodes : Nat) (nodes : Array (Node OracleRef)) (t : Comb) :
    Option (Array (Node OracleRef) × NodeId) :=
  match t with
  | .K =>
      if nodes.size < maxNodes then
        let id := nodes.size
        some (nodes.push (.combK (OracleRef := OracleRef)), id)
      else
        none
  | .S =>
      if nodes.size < maxNodes then
        let id := nodes.size
        some (nodes.push (.combS (OracleRef := OracleRef)), id)
      else
        none
  | .Y =>
      if nodes.size < maxNodes then
        let id := nodes.size
        some (nodes.push (.combY (OracleRef := OracleRef)), id)
      else
        none
  | .app f a => do
      let (nodes1, fId) <- compileAux maxNodes nodes f
      let (nodes2, aId) <- compileAux maxNodes nodes1 a
      if nodes2.size < maxNodes then
        let id := nodes2.size
        some (nodes2.push (.app (OracleRef := OracleRef) fId aId), id)
      else
        none

def compileComb? (maxNodes : Nat) (t : Comb) : Option (State OracleRef) := do
  let (nodes, root) <- compileAux (OracleRef := OracleRef) maxNodes #[] t
  some { nodes := nodes, focus := root, stack := [] }

def wrapOracleSelect (maxNodes : Nat) (s : State OracleRef) (ref : OracleRef)
    (thenTerm elseTerm : Comb) : Option (State OracleRef) := do
  let (nodes1, thenId) <- compileAux (OracleRef := OracleRef) maxNodes s.nodes thenTerm
  let (nodes2, elseId) <- compileAux (OracleRef := OracleRef) maxNodes nodes1 elseTerm
  let base : State OracleRef := { s with nodes := nodes2 }
  let (s1, oId) <- base.pushNode maxNodes (.oracle (OracleRef := OracleRef) ref)
  let (s2, leftId) <- s1.pushNode maxNodes (.app (OracleRef := OracleRef) oId thenId)
  let (s3, rootId) <- s2.pushNode maxNodes (.app (OracleRef := OracleRef) leftId elseId)
  some { s3 with focus := rootId, stack := [] }

inductive StepResult (OracleRef : Type) where
  | progress (s' : State OracleRef)
  | halted (s : State OracleRef)
  | outOfHeap (s : State OracleRef)
deriving Repr

def step (oracleEval : OracleRef → Bool) (maxNodes : Nat) (s : State OracleRef) : StepResult OracleRef :=
  match s.node? s.focus with
  | some (.app f a) =>
      StepResult.progress { s with focus := f, stack := a :: s.stack }
  | some (.combK) =>
      match s.stack with
      | x :: _y :: rest => StepResult.progress { s with focus := x, stack := rest }
      | _ => StepResult.halted s
  | some (.combS) =>
      match s.stack with
      | x :: y :: z :: rest =>
          match s.pushNode maxNodes (.app (OracleRef := OracleRef) x z) with
          | none => StepResult.outOfHeap s
          | some (s1, xz) =>
              match s1.pushNode maxNodes (.app (OracleRef := OracleRef) y z) with
              | none => StepResult.outOfHeap s
              | some (s2, yz) =>
                  match s2.pushNode maxNodes (.app (OracleRef := OracleRef) xz yz) with
                  | none => StepResult.outOfHeap s
                  | some (s3, out) => StepResult.progress { s3 with focus := out, stack := rest }
      | _ => StepResult.halted s
  | some (.combY) =>
      match s.stack with
      | f :: rest =>
          match s.pushNode maxNodes (.app (OracleRef := OracleRef) s.focus f) with
          | none => StepResult.outOfHeap s
          | some (s1, self) =>
              match s1.pushNode maxNodes (.app (OracleRef := OracleRef) f self) with
              | none => StepResult.outOfHeap s
              | some (s2, out) => StepResult.progress { s2 with focus := out, stack := rest }
      | _ => StepResult.halted s
  | some (.oracle ref) =>
      match s.stack with
      | t :: f :: rest =>
          let next := if oracleEval ref then t else f
          StepResult.progress { s with focus := next, stack := rest }
      | _ => StepResult.halted s
  | none => StepResult.halted s

def runFuel (oracleEval : OracleRef → Bool) (maxNodes fuel : Nat) (s : State OracleRef) :
    StepResult OracleRef :=
  match fuel with
  | 0 => StepResult.halted s
  | Nat.succ n =>
      match step oracleEval maxNodes s with
      | StepResult.progress s' => runFuel oracleEval maxNodes n s'
      | StepResult.halted s' => StepResult.halted s'
      | StepResult.outOfHeap s' => StepResult.outOfHeap s'

def headTag? (s : State OracleRef) : Option String :=
  match s.node? s.focus with
  | some (.combK) => some "K"
  | some (.combS) => some "S"
  | some (.combY) => some "Y"
  | some (.app ..) => some "app"
  | some (.oracle ..) => some "oracle"
  | none => none

end State

end SKYMachineBounded

end Combinators
end LoF
end HeytingLean
