module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Partial.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Defs

/-! # Equations between checked numbered RVSDGs with one live token -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires

open CategoryTheory Silmaril.Logic.Institution
open ExplicitRuntime (EntryChecked ThreadedOp boundaryResult)
open OrderedRuntime.Structured (Data Opcode RuntimeValues Threaded Ty)
open RVSDG.Institution (OpcodeMap)

universe u v w
variable {V : Type u} {A B : Partial.Signature.{u,v} V} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

abbrev WireOp (A : Partial.Signature.{u,v} V) := Opcode A.base.pure A.base.effect

/-- Change the instruction while preserving its typed physical ports. -/
def wireOpcodeMap (f : A ⟶ B) : OpcodeMap (WireOp A) (WireOp B)
  | _, _, .ordered i o op => .ordered i o (Partial.Signature.Hom.opcodeMap f op)

/-- Relabel the actual numbered graph, preserving all origins and numbering. -/
def mapGraph (f : A ⟶ B) (g : Graph (WireOp A) args past sigs outs) :
    Graph (WireOp B) args past sigs outs :=
  Institution.mapGraph (wireOpcodeMap f) g

/-- Primitive declarations in the erased dialect retain their unit port. -/
abbrev erasedSignature (A : Partial.Signature.{u,v} V) : Partial.Signature.{u,max u v} V :=
  ⟨⟨ThreadedOp A.base.pure, ThreadedOp A.base.effect⟩⟩

variable {P Q : Dialect.{u,v} V PUnit.{u+1}}

/-- Lift an opcode map to declarations with the same additional unit port. -/
def mapThreadedOpcode (f : OpcodeMap P Q) : OpcodeMap (ThreadedOp P) (ThreadedOp Q)
  | _, _, .op op => .op (f op)

def erasedBaseHom (f : A ⟶ B) : (erasedSignature A).base ⟶ (erasedSignature B).base :=
  ⟨mapThreadedOpcode (P := A.base.pure) (Q := B.base.pure) (Institution.Signature.Hom.pure f.forget),
    mapThreadedOpcode (P := A.base.effect) (Q := B.base.effect) (Institution.Signature.Hom.effect f.forget)⟩

def eraseOpcode (A : Partial.Signature.{u,v} V) : OpcodeMap (WireOp A) (erasedSignature A).base.op
  | _, _, .ordered _ _ op => ExplicitRuntime.eraseInstruction op

def eraseGraph (g : Graph (WireOp A) args past sigs outs) :
    Graph (erasedSignature A).base.op args past sigs outs :=
  Institution.mapGraph (eraseOpcode A) g

/-- The sentence stores real numbered graphs. Admission requires a typed
single-token witness on each decoded graph. The choice of witness is irrelevant. -/
structure Equation (A : Partial.Signature.{u,v} V) where
  args : Ports (Ty V)
  outs : Ports (Ty V)
  inputData : Data args
  outputData : Data outs
  leftSigs : List (Ports (Ty V))
  rightSigs : List (Ports (Ty V))
  lhs : Graph (WireOp A) (Threaded args) [] leftSigs (Threaded outs)
  rhs : Graph (WireOp A) (Threaded args) [] rightSigs (Threaded outs)
  lhsChecked : Nonempty (EntryChecked (a := inputData) (b := outputData) lhs.toTerm)
  rhsChecked : Nonempty (EntryChecked (a := inputData) (b := outputData) rhs.toTerm)

def Equation.erase (e : Equation A) : Partial.Equation (erasedSignature A) :=
  ⟨Threaded e.args, Threaded e.outs, e.leftSigs, e.rightSigs, eraseGraph e.lhs, eraseGraph e.rhs⟩

/-- The established wire denotation, with the output token read from its
physical port and reported alongside the erased tuple. -/
noncomputable def observe (m : Partial.Model.{u,v,w} A σ)
    (g : Graph (WireOp A) (Threaded args) [] sigs (Threaded outs))
    (input : Tuple (RuntimeValues m.value σ) (Threaded args)) :
    Part (OrderedState.Configuration m.value σ (Threaded outs)) :=
  Part.map boundaryResult (NestedTheta.Partial.observe (ExplicitRuntime.Partial.wireModel m) g input)

/-- Compare exact returns and all abnormal endpoints at each explicit input,
including its token. Abnormal comparisons use the actual numbered wire reads. -/
def Equation.Holds (e : Equation A) (m : Partial.Model.{u,v,w} A σ) : Prop :=
  ∀ input : Tuple (RuntimeValues m.value σ) (Threaded e.args),
    observe m e.lhs input = observe m e.rhs input ∧
    ∀ obs, ExplicitRuntime.Partial.abnormal m e.lhs input obs ↔
      ExplicitRuntime.Partial.abnormal m e.rhs input obs

def room (A : Partial.Signature.{u,v} V) (σ : Type (max u w)) :
    Room.{max u v, max (u + 1) v (w + 1), max (u + 1) v (w + 1)} where
  Sen := Equation A
  Mod := Cat.of (Discrete (Partial.Model.{u,v,w} A σ))
  Sat m e := e.Holds m.as

end Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires
