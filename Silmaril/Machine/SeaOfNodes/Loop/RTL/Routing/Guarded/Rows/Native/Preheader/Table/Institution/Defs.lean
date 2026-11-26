module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Denotation.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber.Defs

/-! Finite return observations at the checked word signature. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy WordOp model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber (inputModel)
open Silmaril.SSA.SeaOfNodes.Loop.Institution (Equation Program)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.Institution.Observational (Observation ssaBeh)
open Silmaril.Isotope.Morphism.SSAIter (ScopedRegion)

variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}

/-- Package the original graph at the existing native word signature. -/
def program (g : SourceWithEntry arity entrySigs sigs) :
    Program Rows.wordSignature (wordSorts arity) word :=
  ⟨wordSorts arity, entrySigs, sigs, g⟩

def equation (left : SourceWithEntry arity entrySigs sigs)
    (right : SourceWithEntry arity rightEntry rightSigs) : Equation Rows.wordSignature :=
  ⟨wordSorts arity, word, program left, program right⟩

abbrev LambdaScope (arity : Nat) := ScopedRegion (Primitive WordOp) 1 (wordSorts arity).length

/-- Retain the actual emitted region and obtain its scope from checked typing. -/
def scope {g : SourceWithEntry arity entrySigs sigs} {targets : Checked.Phi.Targets}
    (accepted : lowerChecked g = some targets) : LambdaScope arity :=
  ⟨targets.2, by
    simpa only [Generic.inputContext, Silmaril.SSA.SeaOfNodes.Diamond.dataPorts, List.length_map,
      List.length_singleton] using (lowerChecked_typed accepted).2.scoped⟩

/-- The return projection of the existing observational room at one
typed input and initial memory. -/
def lambdaReturns (input : WordTuple arity) (initial : Memory) (region : LambdaScope arity) :
    Rows.Observation :=
  { result | Observation.ret initial (0, Generic.packResult model (out := word) result.1) result.2 ∈
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) region }

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution
