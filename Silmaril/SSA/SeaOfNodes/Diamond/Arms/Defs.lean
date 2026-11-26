module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs

/-! # A pure diamond with arm-local producers and a tuple join -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms

open RVSDG (Locals Origin Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past : List (List (Ty Data))}
variable {inputs results : List (ValueSort Data)} {sigs : List (List (Ty Data))}

/-- Each arm can read the inputs, shared producers and its own earlier
producers. It supplies one wire per join parameter. -/
structure Arm (Op : Signature.{u,v} Data) (args : List (Ty Data))
    (past : List (List (Ty Data))) (results : List (ValueSort Data)) where
  sigs : List (List (Ty Data))
  dataflow : Dataflow Op args past sigs
  outputs : Wires args (extend past sigs) (dataPorts results)

/-- The shared prefix feeds the If predicate and both arms. The arms and
their output vectors are stored in the Region's predecessor slot order. -/
structure Graph (Op : Signature.{u,v} Data) (inputs : List (ValueSort Data))
    (sigs : List (List (Ty Data))) (results : List (ValueSort Data)) where
  shared : Dataflow Op (dataPorts inputs) [] sigs
  predicate : Origin (dataPorts inputs) (extend [] sigs) (.value .predicate)
  merge : Merge
  arms : Slot → Arm Op (dataPorts inputs) (extend [] sigs) results

variable (m : Model.{u,v,w} Op)

def Arm.eval (arm : Arm Op args past results) (entry : Tuple (Val m.value) args)
    (shared : Locals (Val m.value) past) : Tuple (Val m.value) (dataPorts results) :=
  arm.outputs.read entry (arm.dataflow.eval m entry shared)

variable (g : Graph Op inputs sigs results)
variable (entry : Tuple (Val m.value) (dataPorts inputs))

/-- A finite source run chooses the taken projection and evaluates only the
arm at the corresponding predecessor slot. -/
inductive Graph.Returns : Tuple (Val m.value) (dataPorts results) → Prop where
  | ret {p : Projection} {slot : Slot}
      (branch : Projection.Taken
        (read m g.predicate entry (g.shared.eval m entry PUnit.unit)).down p)
      (arrival : g.merge.predecessor slot = p) :
      Returns ((g.arms slot).eval m entry (g.shared.eval m entry PUnit.unit))

def Graph.denote : Tuple (Val m.value) (dataPorts results) :=
  let shared := g.shared.eval m entry PUnit.unit
  let p := Projection.ofBool (read m g.predicate entry shared).down
  (g.arms (g.merge.slot p)).eval m entry shared

end Silmaril.SSA.SeaOfNodes.Diamond.Arms
