module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Defs

/-! # Lower the whole-memory diamond to one ordered RVSDG γ -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond

open RVSDG (Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Data Opcode Threaded Ty gammaNode nextRuntime runtimePort)
open SeaOfNodes.Diamond (Merge Projection Slot)

variable {args : List ValueSort} {cells : Nat}

def slotIndex : Slot → Fin 2
  | .first => 0
  | .second => 1

def indexSlot : Fin 2 → Slot := Fin.cases .first (fun _ => .second)

abbrev inputPorts (args : List ValueSort) : List (Ty ValueSort) :=
  .control 2 :: dataPorts args

abbrev diamondData (args : List ValueSort) : Data (inputPorts args) :=
  .control (inputData args)

/-- The target selector counts Region positions from zero. The scalar
arguments and sole input heap keep their original order. -/
def encodeEntry (merge : Merge) (guard : Bool) (input : Tuple (Val cells) args)
    (heap : Heap cells) : Tuple (WireVal cells) (Threaded (inputPorts args)) :=
  .cons ⟨slotIndex (merge.slot (Projection.ofBool guard))⟩ (encodeInput heap input)

def Graph.encodeEntry (graph : Graph args) (guard : Bool) (input : Tuple (Val cells) args)
    (heap : Heap cells) : Tuple (WireVal cells) (Threaded (inputPorts args)) :=
  Diamond.encodeEntry graph.merge guard input heap

def argumentWires {entry : List (Ty ValueSort)} {past : List (List (Ty ValueSort))} :
    (sorts : List ValueSort) →
    (∀ {t}, Port (Threaded (dataPorts sorts)) t → Origin entry past t) →
    Wires entry past (dataPorts sorts)
  | [], _ => .nil
  | _ :: rest, wire => .cons (wire .head) (argumentWires rest (fun p => wire (.tail p)))

def captures (args : List ValueSort) : Wires (Threaded (inputPorts args)) [] (dataPorts args) :=
  argumentWires args (fun p => .arg (.tail p))

/-- The suffix receives the γ result word and the original scalar arguments.
Its live heap is wired separately to the γ result's runtime port. -/
def suffixRouting (args : List ValueSort) :
    Routing (.word :: args) [] [Threaded wordPorts] (inputPorts args)
  | _, .arg .head => .output 0 .head
  | _, .arg (.tail p) => .arg (.tail (argumentPort p))
  | _, .output i _ => i.elim0

def Graph.lowered (graph : Graph args) :
    LoweredAt (diamondData args) [] (Threaded wordPorts :: graph.suffix.targetSigs)
      (.arg (runtimePort (inputPorts args))) :=
  let arm := fun j => (graph.arm (graph.merge.predecessor (indexSlot j))).lowered
  let childSigs := fun j => (graph.arm (graph.merge.predecessor (indexSlot j))).targetSigs
  let live := Origin.arg (runtimePort (inputPorts args))
  let suffix := graph.suffix.lowerAt (diamondData args) (suffixRouting args) (nextRuntime [] wordPorts)
  ⟨.bind (gammaNode 0 (.arg .head) live (captures args) childSigs) (fun j => (arm j).term) suffix.term,
    .gamma 0 (.arg .head) live (inputData args) wordData (captures args) childSigs
      (fun j => (arm j).checked) suffix.checked⟩

def Graph.lower (graph : Graph args) :
    RVSDG.Graph (Opcode NoPure Effect) (Threaded (inputPorts args)) []
      (Threaded wordPorts :: graph.suffix.targetSigs) (Threaded wordPorts) :=
  graph.lowered.term.toGraph

end Silmaril.SSA.SeaOfNodes.Memory.Diamond
