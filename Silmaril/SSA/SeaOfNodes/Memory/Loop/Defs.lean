module

public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Defs
public import Silmaril.Semantics.Elgot.Defs

/-!
# A tail-tested Sea of Nodes memory loop

The Loop Region has an entry occurrence and one backedge. Its memory Phi
latches the whole incoming STORE, as in IR ’95 §§2.5 and 3.1–3.2 and
Simple chapter 10's loop memory Phi. The ordered body runs before the If.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop

open RVSDG (Port Tuple)
open SeaOfNodes.Loop (Incoming)

variable {args : List ValueSort} {cells : Nat}

/-- Record whether the table contains a Load and whether it contains a Store. -/
def accesses : {past : List (List ValueSort)} → {version : Nat} →
    Memory.Body args past version → Bool × Bool
  | _, _, .ret .. => (false, false)
  | _, _, .load _ _ rest => (true, (accesses rest).2)
  | _, _, .store _ _ _ rest => ((accesses rest).1, true)

/-- Entry has no previous activation. A backedge carries its producer's last
memory version. -/
abbrev Operand (cells : Nat) (edge : Incoming) : Type :=
  edge.select PUnit (Heap cells)

/-- The memory Phi resolves its input at the arriving occurrence. -/
def latch (initial : Heap cells) : (edge : Incoming) → Operand cells edge → Heap cells
  | .entry, _ => initial
  | .backedge, previous => previous

/-- One ordered memory body and a tail If. The body's word is compared to
the invariant stop argument. Both the compared word and the last Store
version come from the body's typed Return boundary. -/
structure Graph (args : List ValueSort) where
  body : Memory.Graph args
  effects : accesses body = (true, true)
  stop : Port args .word

def Graph.stopWord (graph : Graph args) (input : Tuple (Val cells) args) : Word :=
  input.get graph.stop

/-- Follow explicit memory edges within each activation. A taken backedge
supplies exactly the finished activation's heap as the next Phi operand. -/
inductive Graph.ReturnsFrom (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) :
    (edge : Incoming) → Operand cells edge → Nat → Word → Heap cells → Prop where
  | exit {edge : Incoming} {operand : Operand cells edge} {value : Word} {final : Heap cells}
      (body : graph.body.Returns input (latch initial edge operand) value final)
      (test : value = graph.stopWord input) :
      ReturnsFrom graph input initial edge operand 0 value final
  | backedge {edge : Incoming} {operand : Operand cells edge} {word : Word} {next : Heap cells}
      {count : Nat} {value : Word} {final : Heap cells}
      (body : graph.body.Returns input (latch initial edge operand) word next)
      (test : word ≠ graph.stopWord input)
      (rest : ReturnsFrom graph input initial .backedge next count value final) :
      ReturnsFrom graph input initial edge operand (count + 1) value final

/-- Enter from Start and complete exactly the given number of backedges.
Even a run with zero backedges executes the body once. -/
def Graph.ReturnsAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) (value : Word) (final : Heap cells) : Prop :=
  graph.ReturnsFrom input initial .entry PUnit.unit count value final

def Graph.Returns (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (value : Word) (final : Heap cells) : Prop :=
  ∃ count, graph.ReturnsAfter input initial count value final

/-- Heap-threaded activation: a stop word exits with the updated heap. Any
other word takes a backedge carrying that heap. -/
def Graph.step (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (Word × Heap cells) ⊕ Heap cells :=
  let result := graph.body.denote input heap
  if result.1 = graph.stopWord input then .inl result else .inr result.2

/-- Evaluate from a latched heap with an exact backedge count. -/
def Graph.evalFrom (graph : Graph args) (input : Tuple (Val cells) args) :
    Nat → Heap cells → Option (Word × Heap cells)
  | 0, heap => match graph.step input heap with
    | .inl result => some result
    | .inr _ => none
  | count + 1, heap => match graph.step input heap with
    | .inl _ => none
    | .inr next => graph.evalFrom input count next

/-- Compute a return after exactly this many completed backedges. -/
def Graph.evalAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) : Option (Word × Heap cells) :=
  graph.evalFrom input count initial

/-- The partial fold observes finite returns without imposing a bound. -/
noncomputable def Graph.denote (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) : Part (Word × Heap cells) :=
  Silmaril.Elgot.Part.run (fun heap => Part.some (graph.step input heap)) initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop
