module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Thms
public import Silmaril.SSA.Isotope.Institution.Observational.Thms

/-! The emitted memory diamond in the existing one-exit λSSA observational
room with the shared memory opcode alphabet and the scope of the typed entry. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → NativeSignature, Model → NativeModel, Equation → NativeEquation
open Isotope.Institution.Observational (Observation lambdaSSA)
open Isotope.Morphism.SSAIter (ScopedRegion)

variable {P : NativeSignature} {args : List ValueSort} {cells : Nat}

/-- The existing observational room at the size of the typed entry context. -/
abbrev room (P : NativeSignature) :=
  (lambdaSSA.{0, 0, 0} Opcode 1).inst.I.obj (Discrete.mk (entryContext P.args).length)

/-- Retain the actual emitted CFG and derive scope from its typing. -/
def scope (graph : Graph args) : ScopedRegion Opcode 1 (entryContext args).length :=
  ⟨lower graph, (lower_hasType graph).scoped⟩

/-- Use the existing sentence constructor for equality of all observations. -/
def translateEquation (e : NativeEquation P) :
    Silmaril.Logic.Institution.Observational.Sentence
      (ScopedRegion Opcode 1 (entryContext P.args).length) :=
  .eq (scope e.lhs) (scope e.rhs)

/-- A room model uses exactly the heap instructions of the lowering.
Its bound values are the encoded guard followed by the typed input tuple.
The initial heap is supplied by each observation. -/
def entryModel (m : NativeModel P) (guard : Bool) :
    Isotope.Institution.Observational.Model.{0, 0, 0} Opcode (entryContext P.args).length where
  α := Atom m.cells
  σ := Heap m.cells
  instr := Instruction m.cells
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound i := entryEnv guard m.input i.val

/-- Encode the original observation using the one external exit and the
lowering's packed word. The initial and final heaps are passed through. -/
def returnObservation (initial : Heap cells) (result : Word × Heap cells) :
    Observation (Nat × Isotope.Value (Atom cells)) (Heap cells) :=
  .ret initial (0, packet result.1) result.2

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution
