module

public import Silmaril.SSA.PEG.Simple.Defs

/-! # A typed acyclic graph builder for the SIMPLE frontend

Nodes are emitted over a context of previously emitted sorts. Closing an
empty-prefix builder gives an ordinary numbered PEG with newest node first.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before mid after ins roots : List (Ty Data)} {out : Ty Data}

/-- A prefix extension can reference its initial nodes and anything it has
already emitted. Emitting a node prepends its sort. -/
inductive Code (P : InstructionSet.{u,v} Data) (params before : List (Ty Data)) :
    List (Ty Data) → Type (max u v) where
  | empty : Code P params before before
  | emit {nodes args : List (Ty Data)} {result : Ty Data}
      (prior : Code P params before nodes) (label : Label P params (Fin 0) args result)
      (refs : Tuple (Port nodes) args) : Code P params before (result :: nodes)

def Code.lift : {after : List (Ty Data)} → Code P params before after →
    Port before out → Port after out
  | _, .empty, r => r
  | _, .emit prior _ _, r => .tail (prior.lift r)

def Code.liftRefs (code : Code P params before after) (refs : Tuple (Port before) ins) :
    Tuple (Port after) ins :=
  refs.map fun _ r => code.lift r

def Code.append (prefixCode : Code P params before mid) :
    {after : List (Ty Data)} → Code P params mid after → Code P params before after
  | _, .empty => prefixCode
  | _, .emit prior label nodes => .emit (prefixCode.append prior) label nodes

/-- Read the slots selected by the context of node references. -/
def select {F : Ty Data → Type w} (values : Tuple F before) (refs : Tuple (Port before) ins) :
    Tuple F ins :=
  refs.map fun _ r => values.get r

def Index.zero : Index 0 := Fin.elim0

variable (model : Interpretation.{u,v,w} P)

/-- Every live source slot has the indicated defined value in the node context. -/
def Realizes (values : Tuple (fun t => Option (model.Value t)) before)
    (refs : Tuple (Port before) ins) (store : Tuple model.Value ins) : Prop :=
  ∀ (t : Ty Data) (slot : Port ins t), values.get (refs.get slot) = some (store.get slot)

/-- The local equation of one emitted node. It reuses the PEG interpretation
and asks for the values of its earlier operands. -/
noncomputable def emitValue (input : Tuple model.Value params)
    (label : Label P params (Fin 0) ins out)
    (refs : Tuple (Port before) ins) (values : Tuple (fun t => Option (model.Value t)) before) :
    Option (model.Value out) :=
  label.interpret model input Index.zero fun slot _ _ =>
    values.get (refs.get (portAt ins slot))

/-- Read the equations in emission order. A bottom node does not prevent other
nodes from having values, including a selection of the other branch. -/
noncomputable def Code.eval (input : Tuple model.Value params)
    (base : Tuple (fun t => Option (model.Value t)) before) :
    {after : List (Ty Data)} → Code P params before after → Tuple (fun t => Option (model.Value t)) after
  | _, .empty => base
  | _, .emit prior label nodes =>
    let values := Code.eval input base prior
    .cons (emitValue model input label nodes values) values

structure Row (P : InstructionSet.{u,v} Data) (params nodes : List (Ty Data)) (result : Ty Data) where
  inputs : List (Ty Data)
  label : Label P params (Fin 0) inputs result
  refs : Tuple (Port nodes) inputs

def Row.weaken (r : Row P params before out) (t : Ty Data) : Row P params (t :: before) out :=
  ⟨r.inputs, r.label, r.refs.map fun _ p => .tail p⟩

def Code.row : {after : List (Ty Data)} → Code P params [] after → Port after out → Row P params after out
  | _, .emit _ label refs, .head => ⟨_, label, refs.map fun _ p => .tail p⟩
  | _, .emit prior _ _, .tail p => (prior.row p).weaken _

/-- Turn a typed graph slot into a reference in the numbered PEG table. -/
def numberPort : {nodes : List (Ty Data)} → Port nodes out →
    Ref (fun i : Fin nodes.length => nodes[i]) out
  | _ :: _, .head => ⟨0, rfl⟩
  | _ :: _, .tail p => let r := numberPort p; ⟨r.id.succ, r.typed⟩

def Code.toGraph (code : Code P params [] after) (outputs : Tuple (Port after) roots) :
    Graph P params roots after.length 0 where
  forest := ⟨Fin.elim0⟩
  sort i := after[i]
  node i :=
    let row := code.row (portAt after i)
    .ofLabel row.label (row.refs.map fun _ p => numberPort p)
  roots := outputs.map fun _ p => numberPort p

/-- The typed context of newly emitted node references. -/
structure Build (P : InstructionSet.{u,v} Data) (params before outs : List (Ty Data)) where
  nodes : List (Ty Data)
  code : Code P params before nodes
  refs : Tuple (Port nodes) outs

def Build.keep (refs : Tuple (Port before) roots) : Build P params before roots :=
  ⟨before, .empty, refs⟩

def Build.thenBuild (a : Build P params before ins) (b : Build P params a.nodes roots) :
    Build P params before roots :=
  ⟨b.nodes, a.code.append b.code, b.refs⟩

end Silmaril.SSA.PEG.Simple
