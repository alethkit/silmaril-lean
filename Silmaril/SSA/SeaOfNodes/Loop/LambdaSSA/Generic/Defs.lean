module

public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Defs

/-! # Generate a λSSA CFG for the pure single-loop source profile -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Diamond (Model Val ValueSort dataPorts sortValue)
open Diamond.LambdaSSA (Atom Code Layout Primitive Ref encode encodePort encodeTuple
  inputRefs portCode schedule scheduleLayout scheduledContext shiftRef sortCode terminatorRegion)
open RVSDG (Origin Tuple Wires extend)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region Terminator)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}

def packed (ports : List (Diamond.Ty Data)) : Code Data :=
  PhiView.packedType (ports.map portCode)

/-- Destructure the carried tuple from the front. Each destructuring pushes
the head and the remaining tuple, while retaining older bindings. -/
def unpackContext : List (Code Data) → List (Diamond.Ty Data) → List (Code Data)
  | context, [] => .unit :: context
  | context, port :: rest =>
    unpackContext (portCode port :: packed (port :: rest) :: context) rest

def unpack : List (Diamond.Ty Data) → Region (Primitive Op) → Region (Primitive Op)
  | [], tail => tail
  | _ :: rest, tail => .let₂ (.var 0) (unpack rest tail)

def weakenUnpack : (ports : List (Diamond.Ty Data)) → {context : List (Code Data)} →
    {p : Diamond.Ty Data} → Ref (packed ports :: context) p → Ref (unpackContext context ports) p
  | [], _, _, ref => ref
  | _ :: rest, _, _, ref => weakenUnpack rest (shiftRef (shiftRef ref))

def unpackRefs : (ports : List (Diamond.Ty Data)) → {context : List (Code Data)} →
    Tuple (Ref (unpackContext context ports)) ports
  | [], _ => .nil
  | _ :: rest, _ => .cons (weakenUnpack rest ⟨1, rfl⟩) (unpackRefs rest)

variable (m : Model.{u,v,w} Op)

/-- The environment after the packed parameter has been entered and all its
products destructured. The captured function inputs remain in scope. -/
def unpackEnv : {ports : List (Diamond.Ty Data)} → Tuple (Val m.value) ports →
    Env (Atom m) → Env (Atom m)
  | _, .nil, captured => Isotope.LambdaSSA.Semantics.extend captured .unit
  | _, .cons x rest, captured =>
    unpackEnv rest (Isotope.LambdaSSA.Semantics.extend
      (Isotope.LambdaSSA.Semantics.extend captured (encodeTuple m (.cons x rest))) (encodePort m x))

abbrev inputContext (inputs : List (ValueSort Data)) := (dataPorts inputs).map portCode

def headerStart (inputs carried : List (ValueSort Data)) :
    Layout (headerPorts inputs carried) [] (unpackContext (inputContext inputs) (dataPorts carried)) :=
  ⟨appendTuple (unpackRefs (dataPorts carried))
      ((inputRefs (dataPorts inputs)).map fun _ ref => weakenUnpack (dataPorts carried) (shiftRef ref)),
    PUnit.unit⟩

/-- Convert a typed wire vector to the argument column of a branch leaf. -/
def arguments {args : List (Diamond.Ty Data)} {past : List (List (Diamond.Ty Data))}
    {context : List (Code Data)} (resolve : ∀ {p}, Origin args past p → Ref context p) :
    {ports : List (Diamond.Ty Data)} → Wires args past ports →
      PhiView.Arguments context (ports.map portCode)
  | _, .nil => fun i => (Nat.not_lt_zero _ i.isLt).elim
  | _, .cons wire rest => fun i => Fin.cases (resolve wire) (arguments resolve rest) i

variable (g : Graph Op inputs carried entrySigs headerSigs out)

abbrev entryContext := scheduledContext (inputContext inputs) entrySigs
abbrev headerContext := scheduledContext (unpackContext (inputContext inputs) (dataPorts carried)) headerSigs

def entryLayout : Layout (dataPorts inputs) (extend [] entrySigs) (entryContext (inputs := inputs) (entrySigs := entrySigs)) :=
  scheduleLayout g.preheader (Layout.initial (dataPorts inputs))

def headerLayout :
    Layout (headerPorts inputs carried) (extend [] headerSigs)
      (headerContext (inputs := inputs) (carried := carried) (headerSigs := headerSigs)) :=
  scheduleLayout g.header (headerStart inputs carried)

def entryArgs : PhiView.Arguments (entryContext (inputs := inputs) (entrySigs := entrySigs))
    ((dataPorts carried).map portCode) :=
  arguments (entryLayout g).resolve (g.phiInputs .entry)

def feedbackArgs : PhiView.Arguments
    (.unit :: headerContext (inputs := inputs) (carried := carried) (headerSigs := headerSigs))
    ((dataPorts carried).map portCode) :=
  arguments (fun wire => shiftRef ((headerLayout g).resolve wire)) (g.phiInputs .backedge)

def exitArgs : PhiView.Arguments
    (.unit :: headerContext (inputs := inputs) (carried := carried) (headerSigs := headerSigs))
    [sortCode out] :=
  arguments (fun wire => shiftRef ((headerLayout g).resolve wire)) (.cons g.result .nil)

inductive Site where
  | preheader
  | header

def terminators : Site → Terminator (Primitive Op)
  | .preheader => .br 0 (PhiView.packTerm (entryArgs g))
  | .header => .case (.var ((headerLayout g).resolve g.predicate).val)
      (.br 0 (PhiView.packTerm (feedbackArgs g))) (.br 1 (PhiView.packTerm (exitArgs g)))

def sourceTyping : PhiView.SourceTyping (τ := Code Data) (terminators g) where
  context
    | .preheader => entryContext (inputs := inputs) (entrySigs := entrySigs)
    | .header => headerContext (inputs := inputs) (carried := carried) (headerSigs := headerSigs)
  cases
    | .preheader => .jump
    | .header => .case (A := .unit) (B := .unit)
        (.var ((headerLayout g).resolve g.predicate).property) .jump .jump

def parameters (carried : List (ValueSort Data)) (out : ValueSort Data) : Nat → List (Code Data)
  | 0 => (dataPorts carried).map portCode
  | 1 => [sortCode out]
  | _ + 2 => []

def blockArgs : PhiView.BlockArgs (sourceTyping g) (parameters carried out)
  | ⟨.preheader, .jump⟩ => ⟨entryArgs g, rfl⟩
  | ⟨.header, .left .jump⟩ => ⟨feedbackArgs g, rfl⟩
  | ⟨.header, .right .jump⟩ => ⟨exitArgs g, rfl⟩

def phiView : PhiView.View (sourceTyping g) (parameters carried out) :=
  PhiView.ofBlockArgs (blockArgs g)

def edge : Incoming → PhiView.EdgeOcc (terminators g)
  | .entry => ⟨.preheader, .jump⟩
  | .backedge => ⟨.header, .left .jump⟩

def entry : Region (Primitive Op) :=
  schedule g.preheader (Layout.initial (dataPorts inputs)) (terminatorRegion (terminators g .preheader))

/-- Emit the header table and its branch in the context after unpacking. -/
def body : Region (Primitive Op) :=
  schedule g.header (headerStart inputs carried) (terminatorRegion (terminators g .header))

def header : Region (Primitive Op) := unpack (dataPorts carried) (body g)

def blocks : Fin 1 → Region (Primitive Op) := fun _ => header g

def lower : Region (Primitive Op) := .cfg (entry g) 1 (blocks g)

def packResult (result : sortValue m.value out) : Value (Atom m) := .pair (encode m result) .unit

def stepLabel : sortValue m.value out ⊕ Tuple (Val m.value) (dataPorts carried) → Nat
  | .inl _ => 1
  | .inr _ => 0

def stepPayload :
    sortValue m.value out ⊕ Tuple (Val m.value) (dataPorts carried) → Value (Atom m)
  | .inl result => packResult m result
  | .inr next => encodeTuple m next

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
