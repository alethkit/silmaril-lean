module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs

/-! # Forward a first Load through a scalar loop Φ -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried

open RVSDG (Locals Origin Port Tuple)
open Memory.Forwarding.Disjoint (Certificate)

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
  /-- One-based version published by the Store that feeds the scalar Φ. -/
  storeVersion : Nat

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
  stored : Option Word

/-- Evaluate the native table once and retain the scalar operand at the
selected Store. Later effects still run in their original order. -/
def runWithStore (input : Tuple (Val cells) args) (requested : Nat) :
    {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version →
    Locals (Val cells) past → Heap cells → Option Word → Activation cells
  | _, _, .ret _ value, locals, heap, saved => ⟨(readValue value input locals, heap), saved⟩
  | _, _, .load _ address rest, locals, heap, saved =>
    runWithStore input requested rest (.cons (heap.read (readValue address input locals)) .nil, locals) heap saved
  | _, version, .store _ address value rest, locals, heap, saved =>
    let stored : Word := readValue value input locals
    let next := if version + 1 = requested then some stored else saved
    runWithStore input requested rest locals (heap.write (readValue address input locals) stored) next

def Graph.activateWithStore (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    Activation cells :=
  runWithStore input graph.storeVersion graph.body (.cons header.word .nil, PUnit.unit) header.heap none

def Graph.stopWord (graph : Graph args) (input : Tuple (Val cells) args) : Word :=
  input.get graph.stop

/-- Test and return the original exported word. Feedback carries the
selected Store operand and the final heap. -/
def Graph.step (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells) :
    (Word × Heap cells) ⊕ Header cells :=
  let activation := graph.activateWithStore input header
  let result := activation.result
  if result.1 = graph.stopWord input then .inl result
  else .inr ⟨activation.stored.getD result.1, result.2⟩

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

/-- Track whether the nominated Store supplies the observed cell at Return.
Each later Store must be covered by the certificate. -/
def storeSurvivesAt (facts : Certificate args) (requested : Nat) :
    {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version → Bool → Bool
  | _, _, .ret _ _, matched => matched
  | _, _, .load _ _ rest, matched => storeSurvivesAt facts requested rest matched
  | _, version, .store _ address _ rest, matched =>
    let next := if version + 1 = requested then facts.matches address
      else matched && (!facts.matches address && facts.covers address)
    storeSurvivesAt facts requested rest next

/-- Forward a nominated Store to the next activation under explicit
cell inequalities for the suffix writers. -/
def rewriteWith (source : Loop.Graph args) (storeVersion : Nat) (facts : Certificate args) :
    Option (Graph args) :=
  match source.body with
  | .load _ address rest =>
    if facts.matches address && storeSurvivesAt facts storeVersion rest false then
      some ⟨facts.observed, rest, source.stop, storeVersion⟩
    else none
  | _ => none

/-- Check the concrete typed cell inequalities at the invocation. -/
def rewriteChecked (source : Loop.Graph args) (storeVersion : Nat) (facts : Certificate args)
    (input : Tuple (Val cells) args) : Option (Graph args) :=
  if facts.check input then rewriteWith source storeVersion facts else none

/-- Return observes this exact version of the ordered memory chain. -/
def finalVersion : {past : List (List ValueSort)} → {version : Nat} → Memory.Body args past version → Nat
  | _, _, .ret memory _ => memory.producer.val
  | _, _, .load _ _ rest => finalVersion rest
  | _, _, .store _ _ _ rest => finalVersion rest

/-- The final-Store case requires no inequalities. -/
def rewrite (source : Loop.Graph args) : Option (Graph args) :=
  match source.body with
  | .load _ (.arg address) _ => rewriteWith source (finalVersion source.body) ⟨address, []⟩
  | _ => none

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried
