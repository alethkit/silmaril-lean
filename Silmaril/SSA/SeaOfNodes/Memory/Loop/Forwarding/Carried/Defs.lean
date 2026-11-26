module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs

/-! # Forward a first Load through a scalar loop Φ -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried

open RVSDG (Port Tuple)

variable {args : List ValueSort} {cells : Nat}

/-- The scalar and memory Φ operands for one activation. -/
structure Header (cells : Nat) where
  word : Word
  heap : Heap cells

/-- The native suffix uses its first typed local for the carried word.
The original arguments remain captured for the entire run. -/
structure Graph (args : List ValueSort) where
  address : Port args .address
  body : Memory.Body args [[.word]] 0
  stop : Port args .word

def Graph.Agrees (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) : Prop :=
  header.word = header.heap.read (input.get graph.address)

/-- The entry table reads the cell once and exports the same memory version. -/
def Graph.entry (graph : Graph args) : Memory.Graph args :=
  .load (.latest 0) (.arg graph.address)
    (.ret (.latest 0) (.output (0 : Fin 1) .head))

def Graph.seed (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    Header cells :=
  let result := graph.entry.denote input initial
  ⟨result.1, result.2⟩

def Graph.activate (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    Word × Heap cells :=
  graph.body.denote input (.cons header.word .nil, PUnit.unit) header.heap

def Graph.stopWord (graph : Graph args) (input : Tuple (Val cells) args) : Word :=
  input.get graph.stop

/-- Test the exported word after all effects. A backedge latches it
alongside the final heap of the same activation. -/
def Graph.step (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    (Word × Heap cells) ⊕ Header cells :=
  let result := graph.activate input header
  if result.1 = graph.stopWord input then .inl result else .inr ⟨result.1, result.2⟩

def Graph.evalFrom (graph : Graph args) (input : Tuple (Val cells) args) :
    Nat → Header cells → Option (Word × Heap cells)
  | 0, header => match graph.step input header with
    | .inl result => some result
    | .inr _ => none
  | count + 1, header => match graph.step input header with
    | .inl _ => none
    | .inr next => graph.evalFrom input count next

/-- Count completed backedges. The zero case executes one activation. -/
def Graph.evalAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) : Option (Word × Heap cells) :=
  graph.evalFrom input count (graph.seed input initial)

def Graph.Returns (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (word : Word) (final : Heap cells) : Prop :=
  ∃ count, graph.evalAfter input initial count = some (word, final)

/-- The Return's memory edge names the most recent Store when the table has one. -/
def finalVersion : {past : List (List ValueSort)} → {version : Nat} →
    Memory.Body args past version → Nat
  | _, _, .ret memory _ => memory.producer.val
  | _, _, .load _ _ rest => finalVersion rest
  | _, _, .store _ _ _ rest => finalVersion rest

/-- Remove the first Load if the final Store writes to its original address
port and its stored word is the exact wire exported to the loop test.
The untouched suffix gets the original Load's local from the scalar Φ. -/
def rewrite (source : Loop.Graph args) : Option (Graph args) :=
  match source.body with
  | .load _ (.arg address) rest =>
    if Memory.Forwarding.checkExit source.body address (finalVersion source.body) then
      some ⟨address, rest, source.stop⟩
    else none
  | _ => none

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried
