module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Defs

/-! Finite observations of the actual λSSA and numbered θ lowerings,
at one typed entry valuation and initial heap. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.LambdaSSA (Atom Instruction Opcode inputEnv wordPacket)
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Region (Eval)

variable {P : EntrySignature} {args : List ValueSort}

/-- The ordinary λSSA region with its exact typed entry and one packed exit. -/
abbrev LambdaProgram (args : List ValueSort) :=
  {region : Region Opcode // region.HasType (LambdaSSA.inputContext args) [wordPacket]}

def lowerLambda (graph : Graph args) : LambdaProgram args :=
  ⟨LambdaSSA.lower graph, LambdaSSA.lower_hasType graph⟩

/-- Use standard finite region evaluation and retain its label, payload and
whole final heap at the given initial heap. -/
def lambdaReturns (program : LambdaProgram P.args) (model : EntryModel P) (initial : Heap model.cells)
    (label : Nat) (payload : Value (Atom model.cells)) (final : Heap model.cells) : Prop :=
  Eval (Instruction model.cells) (inputEnv model.input) program.val initial label payload final

def lambdaHolds (e : Equation P) (model : EntryModel P) : Prop :=
  ∀ initial label payload final,
    lambdaReturns (lowerLambda e.lhs) model initial label payload final ↔
      lambdaReturns (lowerLambda e.rhs) model initial label payload final

abbrev thetaSignature : RVSDG.Institution.Signature ValueSort PUnit := ⟨ThetaOpcode⟩

/-- Read the existing partial RVSDG observation at its encoded entry. The
result tuple has the word and the explicit final heap wire. -/
noncomputable def thetaObservation (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) : Part (Tuple (WireVal model.cells) (Threaded wordPorts)) :=
  RVSDG.NestedTheta.Institution.RuntimeObservation.observe (P := thetaSignature)
    (thetaRuntime model.cells) graph.lowerTheta (encodeInput initial model.input)

def thetaHolds (e : Equation P) (model : EntryModel P) : Prop :=
  ∀ initial, thetaObservation e.lhs model initial = thetaObservation e.rhs model initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering
