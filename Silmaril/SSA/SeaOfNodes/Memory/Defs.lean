module

public import Silmaril.SSA.RVSDG.Defs
public import Mathlib.Logic.Function.Basic

/-!
# A straight-line Sea of Nodes memory fragment

Start produces memory version zero. A Store consumes the latest version and
produces a successor. A Load reads that version and produces only a scalar.
Return reads the latest version and a scalar. The program table fixes one
effect order, including reads followed by overwriting stores.

The memory edges follow Click and Paleczny, IR ’95 §2.5 and Fig. 6, and
Simple chapter 10's whole-memory graph. Return consumes current memory as
in Simple. This profile exposes that final memory as part of the result.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#one-memory-value)
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory

open RVSDG (Locals Origin Tuple Wires)

abbrev Address (cells : Nat) := Fin cells
abbrev Word := BitVec 64

/-- A fixed collection of initialized, word-sized cells. -/
abbrev Heap (cells : Nat) := Address cells → Word

def Heap.read {cells : Nat} (heap : Heap cells) (address : Address cells) : Word :=
  heap address

def Heap.write {cells : Nat} (heap : Heap cells) (address : Address cells) (value : Word) :
    Heap cells :=
  Function.update heap address value

inductive ValueSort where
  | address
  | word

def Val (cells : Nat) : ValueSort → Type
  | .address => Address cells
  | .word => Word

/-- A memory edge names Start (0) or a Store (its one-based ordinal).
Admission requires the named producer to be the current memory version. -/
structure MemoryInput (version : Nat) where
  producer : Fin (version + 1)
  current : producer = Fin.last version

def MemoryInput.latest (version : Nat) : MemoryInput version :=
  ⟨Fin.last version, rfl⟩

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}

/-- A typed vertex table with scalar producers in scope and a separate
memory chain. A Store adds a memory producer. A Load adds a scalar
producer at the front of the local scope and leaves the memory edge live. -/
inductive Body (args : List ValueSort) : List (List ValueSort) → Nat → Type where
  | ret {past : List (List ValueSort)} {version : Nat} (memory : MemoryInput version) (value : Origin args past .word) :
      Body args past version
  | load {past : List (List ValueSort)} {version : Nat} (memory : MemoryInput version) (address : Origin args past .address)
      (rest : Body args ([.word] :: past) version) : Body args past version
  | store {past : List (List ValueSort)} {version : Nat} (memory : MemoryInput version) (address : Origin args past .address)
      (value : Origin args past .word) (rest : Body args past (version + 1)) : Body args past version

/-- At Start there are no local scalar producers and no previous stores. -/
abbrev Graph (args : List ValueSort) := Body args [] 0

def readValue {sort : ValueSort} (wire : Origin args past sort)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) : Val cells sort :=
  (Wires.read (.cons wire .nil) input locals).get .head

abbrev Snapshots (cells version : Nat) := Fin (version + 1) → Heap cells

/-- Publish the Store at the next version while retaining earlier snapshots. -/
def Snapshots.push (states : Snapshots cells version) (updated : Heap cells) :
    Snapshots cells (version + 1) :=
  Fin.lastCases updated states

/-- The ordered rules read memory through the producer named at each vertex. -/
inductive Body.Exec (input : Tuple (Val cells) args) :
    {past : List (List ValueSort)} → {version : Nat} → Body args past version →
      Locals (Val cells) past → Snapshots cells version → Word → Heap cells → Prop where
  | ret {past : List (List ValueSort)} {version : Nat} (memory : MemoryInput version) (value : Origin args past .word)
      (locals : Locals (Val cells) past) (states : Snapshots cells version) :
      Exec input (.ret memory value) locals states (readValue value input locals)
        (states memory.producer)
  | load {past : List (List ValueSort)} {version : Nat} {memory : MemoryInput version} {address : Origin args past .address}
      {rest : Body args ([.word] :: past) version} {locals : Locals (Val cells) past}
      {states : Snapshots cells version} {value : Word} {final : Heap cells}
      (next : Exec input rest
        (.cons ((states memory.producer).read (readValue address input locals)) .nil, locals)
        states value final) :
      Exec input (.load memory address rest) locals states value final
  | store {past : List (List ValueSort)} {version : Nat} {memory : MemoryInput version} {address : Origin args past .address}
      {source : Origin args past .word} {rest : Body args past (version + 1)}
      {locals : Locals (Val cells) past} {states : Snapshots cells version}
      {value : Word} {final : Heap cells}
      (next : Exec input rest locals (states.push ((states memory.producer).write
          (readValue address input locals) (readValue source input locals))) value final) :
      Exec input (.store memory address source rest) locals states value final

/-- Interpret the straight-line program by threading just one current heap. -/
def Body.denote (input : Tuple (Val cells) args) :
    {past : List (List ValueSort)} → {version : Nat} → Body args past version →
      Locals (Val cells) past → Heap cells → Word × Heap cells
  | _, _, .ret _ source, locals, heap => (readValue source input locals, heap)
  | _, _, .load _ address rest, locals, heap =>
    rest.denote input (.cons (heap.read (readValue address input locals)) .nil, locals) heap
  | _, _, .store _ address source rest, locals, heap =>
    rest.denote input locals (heap.write (readValue address input locals) (readValue source input locals))

def Graph.Returns (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells)
    (value : Word) (final : Heap cells) : Prop :=
  graph.Exec input PUnit.unit (fun _ => initial) value final

def Graph.denote (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    Word × Heap cells :=
  Body.denote input graph PUnit.unit initial

end Silmaril.SSA.SeaOfNodes.Memory
