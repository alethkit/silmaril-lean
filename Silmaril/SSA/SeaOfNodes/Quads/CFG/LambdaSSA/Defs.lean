module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Run.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs

/-! # Typed lambda-SSA lowering of an ordered quad CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA

open RVSDG (Port Tuple Wires extend)
open Diamond (ValueSort dataPorts sortValue)
open Diamond.LambdaSSA (Atom Layout Primitive Ref encode encodeTuple inputEnv portCode
  schedule scheduleLayout scheduledContext shiftRef sortCode terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region)
open Loop.LambdaSSA.Generic (arguments packed unpack unpackContext unpackRefs)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {n : Nat}
variable {graph : Graph Op regs n} {source : Fin n}

/-- The selected incoming definition and the definition bound by the
destination header, at the same typed register slot. -/
structure Binding (n : Nat) where
  incoming : Version n
  bound : Version n

def Binding.lift (binding : Binding n) : Binding (n + 1) :=
  ⟨binding.incoming.lift, binding.bound.lift⟩

def binding : {n : Nat} → {graph : Graph Op regs n} → {source : Fin n} →
    Edge graph source → {t : Diamond.Ty Data} → Port (dataPorts regs) t → Binding n
  | _, _, _, .latest (prior := prior) (preds := preds) occurrence, _, port =>
    ⟨((prior.column preds occurrence).get port).lift,
      Inputs.version ((prior.header preds).get port)⟩
  | _, _, _, .earlier edge, _, port => (binding edge port).lift

/-- Read the selected entry header using the actual source column. -/
def headerBank (m : Diamond.Model.{u, v, w} Op) (input : Bank m regs) :
    {n : Nat} → {graph : Graph Op regs n} → {source : Fin n} →
    Edge graph source → Path graph source → Option (Bank m regs)
  | _, _, _, .latest (prior := prior) (preds := preds) occurrence, path => do
    let older ← path.unlift.values m input
    readBank (dataPorts regs) ((prior.header preds).read older
      (older.read (prior.column preds occurrence)))
  | _, _, _, .earlier edge, path => headerBank m input edge path.unlift

/-- Sibling lambda-SSA blocks receive their available definitions through
one packed parameter. Include inherited values in the same bank as fresh Φs. -/
abbrev bankTypes (regs : List (ValueSort Data)) := (dataPorts regs).map portCode
abbrev bankCode (regs : List (ValueSort Data)) := packed (dataPorts regs)
abbrev returnCode (out : ValueSort Data) := packed [.value out]

def parameters (regs : List (ValueSort Data)) (out : ValueSort Data) (n label : Nat) :
    List (Silmaril.Ty Data) :=
  if label < n then bankTypes regs else [sortCode out]

abbrev bodyContext (regs : List (ValueSort Data)) := unpackContext (bankTypes regs) (dataPorts regs)

def startLayout (regs : List (ValueSort Data)) :
    Layout (dataPorts regs) [] (bodyContext regs) :=
  ⟨unpackRefs (dataPorts regs), PUnit.unit⟩

abbrev producers (graph : Graph Op regs n) (source : Fin n) :=
  (graph.body source).producers

abbrev bodyPast (graph : Graph Op regs n) (source : Fin n) :=
  extend [] (producers graph source)

abbrev finalContext (graph : Graph Op regs n) (source : Fin n) :=
  scheduledContext (bodyContext regs) (producers graph source)

def transfer (graph : Graph Op regs n) (source : Fin n) :
    Loop.Transfer Op regs (dataPorts regs) [] (producers graph source) :=
  compileBlock (graph.body source) (initial regs)

def finalLayout (graph : Graph Op regs n) (source : Fin n) :
    Layout (dataPorts regs) (bodyPast graph source) (finalContext graph source) :=
  scheduleLayout (transfer graph source).flow (startLayout regs)

/-- The outgoing wire implements the selected occurrence's version binding at
this typed slot. The names are erased when emitting ordinary branch arguments. -/
structure BoundOperand (graph : Graph Op regs n) (source : Fin n) (t : Diamond.Ty Data) where
  versions : Binding n
  wire : RVSDG.Origin (dataPorts regs) (bodyPast graph source) t

def boundOperand (edge : Edge graph source) {t : Diamond.Ty Data} (port : Port (dataPorts regs) t) :
    BoundOperand graph source t :=
  ⟨binding edge port, (transfer graph source).outgoing.get port⟩

def packetWires (edge : Edge graph source) :
    Wires (dataPorts regs) (bodyPast graph source) (dataPorts regs) :=
  tabulate _ (fun port => (boundOperand edge port).wire)

abbrev Resolver (graph : Graph Op regs n) (source : Fin n) (context : List (Silmaril.Ty Data)) :=
  ∀ {t}, RVSDG.Origin (dataPorts regs) (bodyPast graph source) t → Ref context t

variable {context : List (Silmaril.Ty Data)}

theorem parameters_inside (target : Fin n) :
    parameters regs out n target.val = bankTypes regs := by simp [parameters, target.isLt]

theorem parameters_return :
    parameters regs out n n = ([.value out] : List (Diamond.Ty Data)).map portCode := by
  simp [parameters, portCode]

def jumpArgs (resolve : Resolver graph source context) (edge : Edge graph source) :
    PhiView.Arguments context (parameters regs out n edge.target.val) :=
  (parameters_inside edge.target).symm ▸ arguments resolve (packetWires edge)

def returnWires (result : Port (dataPorts regs) (.value out)) :
    Wires (dataPorts regs) (bodyPast graph source) [.value out] :=
  .cons ((transfer graph source).outgoing.get result) .nil

def returnArgs (resolve : Resolver graph source context) (result : Port (dataPorts regs) (.value out)) :
    PhiView.Arguments context (parameters regs out n n) :=
  parameters_return.symm ▸ arguments resolve (returnWires (graph := graph) (source := source) result)

def emit (resolve : Resolver graph source context) :
    Terminator graph source out → Isotope.LambdaSSA.Terminator (Primitive Op)
  | .jump edge => .br edge.target.val (PhiView.packTerm (jumpArgs (out := out) resolve edge))
  | .branch test onTrue onFalse _ =>
    .case (.var (resolve ((transfer graph source).outgoing.get test)).val)
      (.br onTrue.target.val (PhiView.packTerm (jumpArgs (out := out) (fun wire => shiftRef (A := .unit) (resolve wire)) onTrue)))
      (.br onFalse.target.val (PhiView.packTerm (jumpArgs (out := out) (fun wire => shiftRef (A := .unit) (resolve wire)) onFalse)))
  | .ret result => .br n (PhiView.packTerm (returnArgs resolve result))

def casesTyping (resolve : Resolver graph source context) : (term : Terminator graph source out) →
    PhiView.CaseTyping context (emit resolve term)
  | .jump _ => .jump
  | .ret _ => .jump
  | .branch test _ _ _ =>
    .case (A := .unit) (B := .unit) (.var (resolve ((transfer graph source).outgoing.get test)).property)
      .jump .jump

def leafArgs (resolve : Resolver graph source context) : (term : Terminator graph source out) →
    (leaf : PhiView.Successor (emit resolve term)) →
    { args : PhiView.Arguments ((casesTyping resolve term).scope leaf)
        (parameters regs out n leaf.target) // PhiView.packTerm args = leaf.argument }
  | .jump edge, .jump => ⟨jumpArgs resolve edge, rfl⟩
  | .branch _ onTrue _ _, .left .jump => ⟨jumpArgs (fun wire => shiftRef (resolve wire)) onTrue, rfl⟩
  | .branch _ _ onFalse _, .right .jump => ⟨jumpArgs (fun wire => shiftRef (resolve wire)) onFalse, rfl⟩
  | .ret result, .jump => ⟨returnArgs resolve result, rfl⟩

/-- The source edge of each generated leaf. The external return is not a
source CFG edge. -/
def sourceEdge (resolve : Resolver graph source context) : (term : Terminator graph source out) →
    PhiView.Successor (emit resolve term) → Option (Edge graph source)
  | .jump edge, .jump => some edge
  | .branch _ onTrue _ _, .left .jump => some onTrue
  | .branch _ _ onFalse _, .right .jump => some onFalse
  | .ret _, .jump => none

def chosenLeaf (resolve : Resolver graph source context) (m : Diamond.Model.{u, v, w} Op)
    (bank : Bank m regs) : (term : Terminator graph source out) → PhiView.Successor (emit resolve term)
  | .jump _ => .jump
  | .branch test _ _ _ => if (bank.get test).down then .left .jump else .right .jump
  | .ret _ => .jump

/-- The generated conditional binds unit in either leaf. -/
def leafEnv {α : Type w} {term : Isotope.LambdaSSA.Terminator (Primitive Op)} :
    PhiView.Successor term → Isotope.LambdaSSA.Semantics.Env α →
    Isotope.LambdaSSA.Semantics.Env α
  | .jump, env => env
  | .left leaf, env | .right leaf, env => leafEnv leaf (Isotope.LambdaSSA.Semantics.extend env .unit)

variable (program : Program graph out)

def terminators (source : Fin n) : Isotope.LambdaSSA.Terminator (Primitive Op) :=
  emit (finalLayout graph source).resolve (program.terminator source)

def sourceTyping : PhiView.SourceTyping (τ := Silmaril.Ty Data) (terminators program) where
  context := finalContext graph
  cases source := casesTyping (finalLayout graph source).resolve (program.terminator source)

def phiView : PhiView.View (sourceTyping program) (parameters regs out n) :=
  PhiView.ofBlockArgs (fun edge =>
    leafArgs (finalLayout graph edge.source).resolve (program.terminator edge.source) edge.successor)

abbrev selectedOccurrence (m : Diamond.Model.{u, v, w} Op) (bank : Bank m regs) (source : Fin n) :
    PhiView.EdgeOcc (terminators program) :=
  ⟨source, chosenLeaf (finalLayout graph source).resolve m bank (program.terminator source)⟩

abbrev occurrenceEdge (occurrence : PhiView.EdgeOcc (terminators program)) :
    Option (Edge graph occurrence.source) :=
  sourceEdge (finalLayout graph occurrence.source).resolve (program.terminator occurrence.source)
    occurrence.successor

def blocks (source : Fin n) : Region (Primitive Op) :=
  unpack (dataPorts regs)
    (schedule (transfer graph source).flow (startLayout regs) (terminatorRegion (terminators program source)))

def entryArgs (regs : List (ValueSort Data)) : PhiView.Arguments (bankTypes regs) (bankTypes regs) :=
  arguments (Layout.initial (dataPorts regs)).resolve (initial regs)

def lower : Region (Primitive Op) :=
  .cfg (.br graph.start.1.val (PhiView.packTerm (entryArgs regs))) n (blocks program)

def stepLabel {m : Diamond.Model.{u, v, w} Op} : sortValue m.value out ⊕ Edge graph source → Nat
  | .inl _ => n
  | .inr edge => edge.target.val

def stepPayload (m : Diamond.Model.{u, v, w} Op) (bank : Bank m regs) :
    sortValue m.value out ⊕ Edge graph source → Value (Atom m)
  | .inl result => .pair (encode m result) .unit
  | .inr _ => encodeTuple m bank

end Silmaril.SSA.SeaOfNodes.Quads.CFG.LambdaSSA
