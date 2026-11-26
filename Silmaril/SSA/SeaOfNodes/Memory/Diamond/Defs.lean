module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Defs

/-!
# A Sea of Nodes memory diamond

IR ’95 §§2.5 and 3.1 treat the whole STORE as a value and select the
Phi operand at the Region's arriving control input. Simple chapter 10
uses this shape for a conditional store and a load after the join.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond

open RVSDG (Tuple)
open SeaOfNodes.Diamond (Merge Projection Slot)

universe u

/-- Only the arm that has executed publishes a value on its incoming edge. -/
def publish {α : Type u} (edge : Projection) (value : α) : Projection → Option α :=
  fun incoming => if incoming = edge then some value else none

/-- A Phi latches the operand paired with the actual Region input position. -/
def latch {α : Type u} (merge : Merge) (arrival : Slot) (incoming : Projection → Option α) :
    Option α :=
  incoming (merge.predecessor arrival)

/-- One If, two ordered memory arms, and a shared suffix after the Region.
An arm's Return serves as its boundary export. The selected word is the
suffix's first argument and the selected memory version is its Start heap. -/
structure Graph (args : List ValueSort) where
  merge : Merge
  arm : Projection → Memory.Graph args
  suffix : Memory.Graph (.word :: args)

variable {args : List ValueSort} {cells : Nat}

/-- The guard is an evaluated Boolean. Only the taken arm runs from the
initial heap. The Region latches its word and memory at the same occurrence. -/
inductive Graph.Returns (graph : Graph args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) : Word → Heap cells → Prop where
  | ret {edge : Projection} {arrival : Slot} {exported selected : Word × Heap cells}
      {value : Word} {final : Heap cells}
      (taken : Projection.Taken guard edge)
      (arm : (graph.arm edge).Returns input initial exported.1 exported.2)
      (joined : latch graph.merge arrival (publish edge exported) = some selected)
      (suffix : graph.suffix.Returns (.cons selected.1 input) selected.2 value final) :
      Returns graph guard input initial value final

/-- Thread the current heap through the selected arm and then the suffix. -/
def Graph.denote (graph : Graph args) (guard : Bool) (input : Tuple (Val cells) args)
    (initial : Heap cells) : Word × Heap cells :=
  let selected := (graph.arm (Projection.ofBool guard)).denote input initial
  graph.suffix.denote (.cons selected.1 input) selected.2

end Silmaril.SSA.SeaOfNodes.Memory.Diamond
