module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Defs

/-! # Compile a finite chain by linking its packed boundaries -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA

open Diamond.LambdaSSA (Code Primitive initialContext)
open Silmaril.Isotope.LambdaSSA (Region Terminator)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs results : List (ValueSort Data)}

def identityArgs (context : List (Code Data)) : PhiView.Arguments context context :=
  fun i => ⟨i, List.getElem?_eq_getElem i.isLt⟩

/-- The empty chain sends its full input vector to exit zero. Every other
chain links the current diamond's packed join to the compiled suffix. -/
def lower : {inputs results : List (ValueSort Data)} → Chain Op inputs results → Region (Primitive Op)
  | inputs, _, .nil => .br 0 (PhiView.packTerm (identityArgs (initialContext inputs)))
  | _, _, .cons (middle := middle) head tail =>
    Sequential.LambdaSSA.link middle (Arms.LambdaSSA.lower head) (lower tail)

/-- Each local arm terminator is addressed by its stage position and
projection. Local branch labels can recur in different CFG scopes. -/
def terminators : {inputs results : List (ValueSort Data)} → (chain : Chain Op inputs results) →
    Fin chain.length × Projection → Terminator (Primitive Op)
  | _, _, .nil, site => site.1.elim0
  | _, _, .cons head tail, site =>
    Fin.cases (Arms.LambdaSSA.armTerminator head site.2)
      (fun stage => terminators tail (stage, site.2)) site.1

/-- Lift the existing PhiView occurrence into the chain's stage scope,
following that stage's own predecessor slot order. -/
def edge : {inputs results : List (ValueSort Data)} → (chain : Chain Op inputs results) →
    Fin chain.length → Slot → PhiView.EdgeOcc (terminators chain)
  | _, _, .nil, stage, _ => stage.elim0
  | _, _, .cons head tail, stage, slot =>
    Fin.cases (motive := fun _ => PhiView.EdgeOcc (terminators (.cons head tail)))
      (let occurrence := Arms.LambdaSSA.edge head slot
       ⟨((0 : Fin (tail.length + 1)), occurrence.source), occurrence.successor⟩)
      (fun i =>
        let occurrence := edge tail i slot
        ⟨(occurrence.source.1.succ, occurrence.source.2), occurrence.successor⟩) stage

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA
