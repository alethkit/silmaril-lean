module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.PhiView.Defs

/-! # Scheduled lowering of the pure Sea of Nodes diamond to λSSA -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA

open RVSDG (Locals Origin Port PortType Tuple Wires extend)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region Terminator Tm)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}

abbrev Code (Data : Type u) := Silmaril.Ty Data

def sortCode : ValueSort Data → Code Data
  | .predicate => .coprod .unit .unit
  | .data sort => .base sort

def portCode : Ty Data → Code Data
  | .value sort => sortCode sort
  | .control _ => .unit
  | .state impossible => nomatch impossible

/-- One target opcode for each source primitive, with its original profile. -/
inductive Primitive (Op : Signature.{u,v} Data) where
  | apply {ins : List (ValueSort Data)} {out : ValueSort Data} (op : Op ins out)

instance : HasTy (Primitive Op) (Code Data) where
  src
    | .apply (ins := ins) _ => PhiView.packedType ((dataPorts ins).map portCode)
  trg
    | .apply (out := out) _ => sortCode out

variable (m : Model.{u,v,w} Op)

/-- Tags carry the source sort alongside its value. Predicates use the
canonical λSSA sum of units so the target's case selects the control arm. -/
abbrev Atom := (sort : Data) × m.value sort

def encode {sort : ValueSort Data} (value : sortValue m.value sort) : Value (Atom m) :=
  match sort with
  | .predicate => if value.down then .inl .unit else .inr .unit
  | .data sort => .atom ⟨sort, value⟩

def encodePort {port : Ty Data} (value : Val m.value port) : Value (Atom m) :=
  match port with
  | .value _ => encode m value
  | .control _ => .unit
  | .state impossible => nomatch impossible

def encodeTuple : {ports : List (Ty Data)} → Tuple (Val m.value) ports → Value (Atom m)
  | _, .nil => .unit
  | _, .cons a rest => .pair (encodePort m a) (encodeTuple rest)

/-- Interpret only the primitive opcode, on an encoded operand tuple. Each
opcode applies the given total source operation and leaves ambient state alone. -/
def instruction {σ : Type x} :
    Primitive Op → Value (Atom m) → σ → Value (Atom m) → σ → Prop
  | .apply op, argument, start, result, finish =>
    ∃ values, argument = encodeTuple m values ∧
      result = encode m (m.run op values) ∧ finish = start

def inputEnv : {ports : List (Ty Data)} → Tuple (Val m.value) ports → Env (Atom m)
  | _, .nil => fun _ => .unit
  | _, .cons a rest => Isotope.LambdaSSA.Semantics.extend (inputEnv rest) (encodePort m a)

abbrev Ref (context : List (Code Data)) (port : Ty Data) :=
  PhiView.Operand context (portCode port)

def shiftRef {context : List (Code Data)} {port : Ty Data} {A : Code Data}
    (r : Ref context port) : Ref (A :: context) port :=
  ⟨r.val + 1, r.property⟩

def inputRefs : (ports : List (Ty Data)) → Tuple (Ref (ports.map portCode)) ports
  | [] => .nil
  | _ :: rest => .cons ⟨0, rfl⟩ ((inputRefs rest).map fun _ => shiftRef)

/-- The schedule tracks source origins as typed references into the current
λSSA context. Earlier producer results refer to their existing binders. -/
structure Layout (args : List (Ty Data)) (past : List (List (Ty Data)))
    (context : List (Code Data)) where
  argsRefs : Tuple (Ref context) args
  localRefs : Locals (Ref context) past

variable {context : List (Code Data)}

/-- Every typed variable reference reads the encoding of its source port. -/
def TupleMatch (env : Env (Atom m)) {ports : List (Ty Data)}
    (refs : Tuple (Ref context) ports) (values : Tuple (Val m.value) ports) : Prop :=
  ∀ {p} (slot : Port ports p), env (refs.get slot).val = encodePort m (values.get slot)

def LocalsMatch (env : Env (Atom m)) : {past : List (List (Ty Data))} →
    Locals (Ref context) past → Locals (Val m.value) past → Prop
  | [], _, _ => True
  | _ :: _, refs, locals => TupleMatch m env refs.1 locals.1 ∧ LocalsMatch env refs.2 locals.2

/-- The target environment represents the source inputs and all scheduled producers. -/
def LayoutMatch (layout : Layout args past context)
    (env : Env (Atom m)) (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) : Prop :=
  TupleMatch m env layout.argsRefs entry ∧ LocalsMatch m env layout.localRefs locals

def Layout.initial (args : List (Ty Data)) : Layout args [] (args.map portCode) :=
  ⟨inputRefs args, PUnit.unit⟩

def Layout.resolve {context : List (Code Data)} (layout : Layout args past context)
    {port : Ty Data} : Origin args past port → Ref context port
  | .arg p => layout.argsRefs.get p
  | .output i p => (layout.localRefs.get i).get p

def pushLocalRefs {context : List (Code Data)} (out : ValueSort Data) :
    {past : List (List (Ty Data))} → Locals (Ref context) past →
      Locals (Ref (sortCode out :: context)) (past ++ [[.value out]])
  | [], _ => (.cons ⟨0, rfl⟩ .nil, PUnit.unit)
  | _ :: _, refs => (refs.1.map (fun _ => shiftRef), pushLocalRefs out refs.2)

def Layout.push {context : List (Code Data)} (layout : Layout args past context)
    (out : ValueSort Data) : Layout args (past ++ [[.value out]]) (sortCode out :: context) :=
  ⟨layout.argsRefs.map (fun _ => shiftRef), pushLocalRefs out layout.localRefs⟩

/-- Put each producer's result in the newest part of the context. -/
def scheduledContext (context : List (Code Data)) : List (List (Ty Data)) → List (Code Data)
  | [] => context
  | ports :: rest => scheduledContext (ports.map portCode ++ context) rest

def scheduleLayout : {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    {context : List (Code Data)} → Layout args past context →
      Layout args (extend past sigs) (scheduledContext context sigs)
  | _, _, .nil, _, layout => layout
  | _, _, .cons (out := out) _ _ tail, _, layout => scheduleLayout tail (layout.push out)

def wireTerm {context : List (Code Data)} (layout : Layout args past context) :
    {ports : List (Ty Data)} → Wires args past ports → Tm (Primitive Op)
  | _, .nil => .unit
  | _, .cons origin rest => .pair (.var (layout.resolve origin).val) (wireTerm layout rest)

/-- Emit one let per producer in the source's certified dependency order. -/
def schedule : {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    {context : List (Code Data)} → Layout args past context →
      Region (Primitive Op) → Region (Primitive Op)
  | _, _, .nil, _, _, tail => tail
  | _, _, .cons (out := out) op wires rest, _, layout, tail =>
      .let₁ (.op (.apply op) (wireTerm layout wires)) (schedule rest (layout.push out) tail)

abbrev initialContext (inputs : List (ValueSort Data)) := (dataPorts inputs).map portCode

abbrev finalContext (inputs : List (ValueSort Data)) (sigs : List (List (Ty Data))) :=
  scheduledContext (initialContext inputs) sigs

variable (g : Graph Op inputs sigs out)

def finalLayout : Layout (dataPorts inputs) (extend [] sigs) (finalContext inputs sigs) :=
  scheduleLayout g.dataflow (Layout.initial (dataPorts inputs))

def parameters (out : ValueSort Data) : Nat → List (Code Data)
  | 0 => [sortCode out]
  | _ + 1 => []

/-- The sole join parameter in a case-arm scope, where the unit case binder
shifts all producer references by one. -/
def slotArguments (slot : Slot) :
    PhiView.Arguments (.unit :: finalContext inputs sigs) [sortCode out] :=
  fun i => Fin.cases (shiftRef ((finalLayout g).resolve (g.phi.operand slot)))
    (fun j => (Nat.not_lt_zero _ j.isLt).elim) i

def branch (projection : Projection) : Terminator (Primitive Op) :=
  .br 0 (PhiView.packTerm (slotArguments g (g.phi.merge.slot projection)))

def dispatch : Terminator (Primitive Op) :=
  .case (.var ((finalLayout g).resolve g.predicate).val) (branch g .onTrue) (branch g .onFalse)

def sourceTyping : PhiView.SourceTyping (τ := Code Data) (fun _ : Unit => dispatch g) where
  context _ := finalContext inputs sigs
  cases _ := .case (A := .unit) (B := .unit)
    (.var ((finalLayout g).resolve g.predicate).property) .jump .jump

/-- Both projections leave the same terminator and reach label zero. Their
positions in the terminator, rather than the labels, identify the transfers. -/
def projectionEdge : Projection → PhiView.EdgeOcc (fun _ : Unit => dispatch g)
  | .onTrue => ⟨(), .left .jump⟩
  | .onFalse => ⟨(), .right .jump⟩

def edge (slot : Slot) : PhiView.EdgeOcc (fun _ : Unit => dispatch g) :=
  projectionEdge g (g.phi.merge.predecessor slot)

def blockArgs : PhiView.BlockArgs (sourceTyping g) (parameters out)
  | ⟨(), .left .jump⟩ => ⟨slotArguments g (g.phi.merge.slot .onTrue), rfl⟩
  | ⟨(), .right .jump⟩ => ⟨slotArguments g (g.phi.merge.slot .onFalse), rfl⟩

def phiView : PhiView.View (sourceTyping g) (parameters out) :=
  PhiView.ofBlockArgs (blockArgs g)

/-- Include the existing terminator syntax as a region tail. -/
def terminatorRegion : Terminator (Primitive Op) → Region (Primitive Op)
  | .br label arg => .br label arg
  | .case discr l r => .case discr (terminatorRegion l) (terminatorRegion r)

/-- The one local label binds the packed φ parameter, unpacks it, and
transfers its value to label one (external exit zero). -/
def join : Region (Primitive Op) :=
  .let₂ (.var 0) (.br 1 (.var 1))

def lower : Region (Primitive Op) :=
  .cfg (schedule g.dataflow (Layout.initial (dataPorts inputs)) (terminatorRegion (dispatch g)))
    1 (fun _ => join)

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
