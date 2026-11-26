module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs

/-! # An ordinary λSSA CFG with two producer arms and a tuple join -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA

open Diamond.LambdaSSA
open RVSDG (Locals extend)
open Silmaril.Isotope.LambdaSSA (Region Terminator)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past : List (List (Ty Data))} {context : List (Code Data)}
variable {inputs results : List (ValueSort Data)} {sigs : List (List (Ty Data))}

def shiftLocals (A : Code Data) : {past : List (List (Ty Data))} →
    Locals (Ref context) past → Locals (Ref (A :: context)) past
  | [], _ => PUnit.unit
  | _ :: _, refs => (refs.1.map (fun _ => shiftRef), shiftLocals A refs.2)

/-- The block parameter precedes all captured prefix references. -/
def armStart (layout : Layout args past context) : Layout args past (.unit :: context) :=
  ⟨layout.argsRefs.map (fun _ => shiftRef), shiftLocals .unit layout.localRefs⟩

variable (g : Graph Op inputs sigs results)

def sharedLayout : Layout (dataPorts inputs) (extend [] sigs) (finalContext inputs sigs) :=
  scheduleLayout g.shared (Layout.initial (dataPorts inputs))

def selectedArm (p : Projection) : Arm Op (dataPorts inputs) (extend [] sigs) results :=
  g.arms (g.merge.slot p)

abbrev armContext (p : Projection) :=
  scheduledContext (.unit :: finalContext inputs sigs) (selectedArm g p).sigs

def armLayout (p : Projection) :
    Layout (dataPorts inputs) (extend (extend [] sigs) (selectedArm g p).sigs) (armContext g p) :=
  scheduleLayout (selectedArm g p).dataflow (armStart (sharedLayout g))

def armArgs (p : Projection) : PhiView.Arguments (armContext g p) ((dataPorts results).map portCode) :=
  Loop.LambdaSSA.Generic.arguments (armLayout g p).resolve (selectedArm g p).outputs

def armTerminator (p : Projection) : Terminator (Primitive Op) :=
  .br 2 (PhiView.packTerm (armArgs g p))

def sourceTyping : PhiView.SourceTyping (τ := Code Data) (armTerminator g) where
  context := armContext g
  cases _ := .jump

def parameters (results : List (ValueSort Data)) : Nat → List (Code Data)
  | 2 => (dataPorts results).map portCode
  | _ => []

def blockArgs : PhiView.BlockArgs (sourceTyping g) (parameters results)
  | ⟨p, .jump⟩ => ⟨armArgs g p, rfl⟩

def phiView : PhiView.View (sourceTyping g) (parameters results) :=
  PhiView.ofBlockArgs (blockArgs g)

def incoming (p : Projection) : PhiView.EdgeOcc (armTerminator g) := ⟨p, .jump⟩

def edge (slot : Slot) : PhiView.EdgeOcc (armTerminator g) := incoming g (g.merge.predecessor slot)

abbrev resultCode (results : List (ValueSort Data)) : Code Data :=
  PhiView.packedType ((dataPorts results).map portCode)

def blockTypes (results : List (ValueSort Data)) : Fin 3 → Code Data :=
  Fin.cases .unit (Fin.cases .unit (fun _ => resultCode results))

/-- Dispatch to the true block at label zero or the false block at label one. -/
def dispatch : Region (Primitive Op) :=
  .case (.var ((sharedLayout g).resolve g.predicate).val) (.br 0 .unit) (.br 1 .unit)

def armBlock (p : Projection) : Region (Primitive Op) :=
  schedule (selectedArm g p).dataflow (armStart (sharedLayout g))
    (terminatorRegion (armTerminator g p))

/-- Label two receives the latched tuple and returns it at external exit zero. -/
def blocks : Fin 3 → Region (Primitive Op) :=
  Fin.cases (armBlock g .onTrue) (Fin.cases (armBlock g .onFalse) (fun _ => .br 3 (.var 0)))

/-- Scheduling the prefix outside the CFG lets both arm blocks capture its
bindings. Each arm schedules its own table inside its block. -/
def lower : Region (Primitive Op) :=
  schedule g.shared (Layout.initial (dataPorts inputs)) (.cfg (dispatch g) 3 (blocks g))

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA
