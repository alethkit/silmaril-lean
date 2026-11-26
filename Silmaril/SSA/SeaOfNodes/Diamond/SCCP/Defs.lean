module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.Semantics.Dataflow.Flat.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Fin

/-! Simultaneous executable-occurrence and constant equations for a pure diamond. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP

open Semantics.Dataflow (Flat)
open RVSDG (PortType Port Tuple Locals Origin Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {value : Data → Type w}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

abbrev Fact (value : Data → Type w) (port : Ty Data) := Flat (Val value port)

/-- A finite pointwise assignment with the source type of each producer port. -/
abbrev ProducerFacts (value : Data → Type w) (sigs : List (List (Ty Data))) :=
  (vertex : Fin sigs.length) → (port : Fin sigs[vertex].length) → Fact value sigs[vertex][port]

/-- Region occurrence numbers follow Region order, independent of If order. -/
def slotIndex : Slot → Fin 2
  | .first => 0
  | .second => 1

abbrev Executable := Finset (Fin 2)

def Marked (edges : Executable) (slot : Slot) : Prop :=
  slotIndex slot ∈ edges

abbrev State (value : Data → Type w) (sigs : List (List (Ty Data))) (out : ValueSort Data) :=
  Executable × (ProducerFacts value (extend [] sigs) × Flat (sortValue value out))

def tupleFacts : {ports : List (Ty Data)} → Tuple (Fact value) ports →
    (i : Fin ports.length) → Fact value ports[i]
  | [], .nil, i => i.elim0
  | _ :: _, .cons head tail, i => Fin.cases head (fun j => tupleFacts tail j) i

def readPort {ports : List (Ty Data)} {t : Ty Data} (port : Port ports t) :
    ((i : Fin ports.length) → Fact value ports[i]) → Fact value t :=
  match port with
  | .head => fun facts => facts 0
  | .tail p => fun facts => readPort p fun i => facts i.succ

def readFact (entry : Tuple (Fact value) args) (facts : ProducerFacts value past)
    {t : Ty Data} : Origin args past t → Fact value t
  | .arg port => entry.get port
  | .output node port => readPort port (facts node)

def TupleCovers {ports : List (Ty Data)} (facts : Tuple (Fact value) ports) (entry : Tuple (Val value) ports) :
    Prop :=
  ∀ {t} (port : Port ports t), (facts.get port).Covers (entry.get port)

def LocalsCover (facts : Locals (Fact value) past) (locals : Locals (Val value) past) : Prop :=
  ∀ vertex, TupleCovers (facts.get vertex) (locals.get vertex)

/-- Collect all operands of a total primitive. An unknown operand delays
evaluation; overdefinition propagates when all operands have evidence. -/
def gather : {ports : List (Ty Data)} → Tuple (Fact value) ports → Flat (Tuple (Val value) ports)
  | [], .nil => .constant .nil
  | _ :: _, .cons head tail => Flat.map₂ Tuple.cons head (gather tail)

/-- The acyclic producer slice uses the existing ranked table. Every producer
is executed before the branch in this profile. -/
def evalFacts (m : Model.{u, v, w} Op) (entry : Tuple (Fact m.value) args) :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    Locals (Fact m.value) past → Locals (Fact m.value) (extend past sigs)
  | _, _, .nil, locals => locals
  | past, _, .cons (sigs := tail) (out := out) op wires rest, locals =>
    let head : List (Ty Data) := [.value out]
    let result : Tuple (Fact m.value) head :=
      .cons (Flat.map (m.run op) (gather (wires.read entry locals))) .nil
    evalFacts m entry (past := past ++ [head]) (sigs := tail) rest (locals.snoc result)

def factsOfLocals (locals : Locals (Fact value) sigs) : ProducerFacts value sigs :=
  fun i => tupleFacts (locals.get i)

def producerFacts (m : Model.{u, v, w} Op) (g : Graph Op inputs sigs out)
    (entry : Tuple (Fact m.value) (dataPorts inputs)) : ProducerFacts m.value (extend [] sigs) :=
  factsOfLocals (evalFacts m entry g.dataflow PUnit.unit)

/-- A known predicate marks its precise Region occurrence. An overdefined
predicate permits either projection. Bottom defers the decision. -/
def branchEdges (merge : Merge) : Flat (ULift.{w} Bool) → Executable
  | .bottom => ∅
  | .constant test => {slotIndex (merge.slot (Projection.ofBool test.down))}
  | .overdefined => Finset.univ

def gate {α : Type*} (edges : Executable) (slot : Slot) (fact : Flat α) : Flat α :=
  if slotIndex slot ∈ edges then fact else ⊥

def phiFact [DecidableEq (sortValue value out)] (phi : Phi args past out) (edges : Executable)
    (entry : Tuple (Fact value) args) (facts : ProducerFacts value past) : Flat (sortValue value out) :=
  Flat.join
    (gate edges .first (readFact entry facts (phi.operand .first)))
    (gate edges .second (readFact entry facts (phi.operand .second)))

/-- One simultaneous step. The control and Phi equations read the previous
assignment. The ranked producer slice depends only on the entry facts. -/
def transfer (m : Model.{u, v, w} Op) [DecidableEq (sortValue m.value out)]
    (g : Graph Op inputs sigs out) (entry : Tuple (Fact m.value) (dataPorts inputs))
    (old : State m.value sigs out) : State m.value sigs out :=
  (branchEdges g.phi.merge (readFact entry old.2.1 g.predicate),
    producerFacts m g entry,
    phiFact g.phi old.1 entry old.2.1)

/-- The occurrence selected by the native diamond evaluator. -/
def takenSlot (m : Model.{u, v, w} Op) (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) : Slot :=
  g.phi.merge.slot (Projection.ofBool
    (read m g.predicate entry (g.dataflow.eval m entry PUnit.unit)).down)

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP
