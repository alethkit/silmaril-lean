module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs

/-! # Forward a first Load through a scalar loop Φ -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried

open RVSDG (Locals Port Tuple)
open Memory.Forwarding (originKey)

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

structure Activation (cells : Nat) where
  result : Word × Heap cells
  lastStored : Option Word

/-- Evaluate the native table once, retaining the actual scalar operand of
each Store when it writes. Loads and Return leave that scalar in place. -/
def runWithLastStore (input : Tuple (Val cells) args) :
    {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version →
    Locals (Val cells) past → Heap cells → Option Word → Activation cells
  | _, _, .ret _ value, locals, heap, last => ⟨(readValue value input locals, heap), last⟩
  | _, _, .load _ address rest, locals, heap, last =>
    runWithLastStore input rest (.cons (heap.read (readValue address input locals)) .nil, locals) heap last
  | _, _, .store _ address value rest, locals, heap, _ =>
    let stored := readValue value input locals
    runWithLastStore input rest locals (heap.write (readValue address input locals) stored) (some stored)

def Graph.activateWithStore (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    Activation cells :=
  runWithLastStore input graph.body (.cons header.word .nil, PUnit.unit) header.heap none

def Graph.stopWord (graph : Graph args) (input : Tuple (Val cells) args) : Word :=
  input.get graph.stop

/-- Test and return the original exported word. Feedback carries the last
Store operand and the final heap. A checked rewrite always has a Store. -/
def Graph.step (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    (Word × Heap cells) ⊕ Header cells :=
  let activation := graph.activateWithStore input header
  let result := activation.result
  if result.1 = graph.stopWord input then .inl result
  else .inr ⟨activation.lastStored.getD result.1, result.2⟩

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

/-- Check whether the last Store writes to this original argument port.
Each Store replaces the previous fact. Return observes the live version. -/
def lastStoreMatchesAt (observed : Port args .address) :
    {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version → Bool → Bool
  | _, _, .ret _ _, matched => matched
  | _, _, .load _ _ rest, matched => lastStoreMatchesAt observed rest matched
  | _, _, .store _ address _ rest, _ =>
    lastStoreMatchesAt observed rest (originKey address == .inl observed.index)

/-- Remove the first Load if the final Store writes to its original address
port. The untouched suffix gets the original Load's local from the scalar Φ. -/
def rewrite (source : Loop.Graph args) : Option (Graph args) :=
  match source.body with
  | .load _ (.arg address) rest =>
    if lastStoreMatchesAt address rest false then
      some ⟨address, rest, source.stop⟩
    else none
  | _ => none

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried
