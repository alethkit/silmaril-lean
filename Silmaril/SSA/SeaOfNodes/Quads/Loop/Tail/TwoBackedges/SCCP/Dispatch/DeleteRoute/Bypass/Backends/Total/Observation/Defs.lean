module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs

/-! Typed execution and word observations for all total compilation outcomes. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF
open Tail.Diamond.MLIR.CF (Widths)
open RVSDG (Tuple)
open RVSDG.NestedTheta
open Blocks (Bank)

structure SourceBudget where
  blocks : Nat

structure CFBudget where
  blocks : Nat

structure ThetaBudget where
  activations : Nat

structure Budgets where
  source : SourceBudget
  cf : CFBudget
  theta : ThetaBudget

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}

/-- Convert a shared feedback limit to the three execution budgets. -/
def Outcome.budgets (outcome : Outcome p) (limit : Nat) : Budgets :=
  let cf : CFBudget := match outcome with
    | .specialized _ => ⟨2 * limit + 3⟩
    | .twoLive _ | .neitherMarked _ => ⟨3 * limit + 3⟩
  ⟨⟨3 * limit + 2⟩, cf, ⟨limit⟩⟩

/-- Only the specialization depends on the input facts. -/
def Outcome.Compatible (outcome : Outcome p) (facts : Tuple (Fact Word) (dataPorts regs))
    (input : Bank (regs := regs) model) : Prop :=
  match outcome with
  | .specialized _ => TupleCovers facts input
  | .twoLive _ | .neitherMarked _ => True

/-- Access the actual CF artifact while retaining its label family. -/
def Outcome.cfTarget (outcome : Outcome p) :
    Σ Label : List Width → Type, Cfg TargetOp Label (Widths regs) [result] :=
  match outcome with
  | .specialized targets => ⟨_, targets.cf⟩
  | .twoLive targets | .neitherMarked targets => ⟨_, targets.cf⟩

/-- Access the actual numbered artifact while retaining its producer table type. -/
def Outcome.numberedTarget (outcome : Outcome p) :
    Σ sigs, Graph (Join.Opcode Op) (dataPorts regs) [] sigs [.value (.data result)] :=
  match outcome with
  | .specialized targets => ⟨_, targets.numbered⟩
  | .twoLive targets | .neitherMarked targets => ⟨_, targets.numbered⟩

def runSource (p : Program Op regs (.data result)) (input : Bank (regs := regs) model)
    (budget : SourceBudget) : Option (Word result) :=
  p.source.runFrom model budget.blocks 0 input

def Outcome.runCF (outcome : Outcome p) (input : Bank (regs := regs) model) (budget : CFBudget) :
    Option (Word result) :=
  (outcome.cfTarget.2.run evalOp budget.blocks (encodeValues input)).map (fun env => env.get .here)

def Outcome.runNumbered (outcome : Outcome p) (input : Bank (regs := regs) model) (budget : ThetaBudget) :
    Option (Word result) :=
  (outcome.numberedTarget.2.run (Join.model model) budget.activations input).map
    (fun values => values.get .head)

/-- The original source's partial return is witnessed by a finite source run. -/
noncomputable def sourcePart (p : Program Op regs (.data result)) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  ⟨∃ value budget, runSource p input budget = some value, fun h => Classical.choose h⟩

/-- Read the word from the actual CF denotation. The pure embedding has no aborts. -/
noncomputable def Outcome.cfPart (outcome : Outcome p) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  ((SwitchAssert.Cfg.embed outcome.cfTarget.2).denotePart evalOp (encodeValues input)).bind fun
    | .returned env => Part.some (env.get .here)
    | .aborted => Part.none

/-- Observe the actual numbered graph in the partial semantics with total primitives. -/
noncomputable def Outcome.numberedPart (outcome : Outcome p) (input : Bank (regs := regs) model) :
    Part (Word result) :=
  (Partial.observe (MonadicModel.ofRuntime (Join.model model)) outcome.numberedTarget.2 input).map
    (fun values => values.get .head)

/-- Both target budgets match the source budget, and finite observations
also match when each runner chooses its own bound. -/
structure Correct (outcome : Outcome p) (input : Bank (regs := regs) model) : Prop where
  bounded (limit : Nat) :
    let budgets := outcome.budgets limit
    outcome.runCF input budgets.cf = runSource p input budgets.source ∧
      outcome.runNumbered input budgets.theta = runSource p input budgets.source
  returns_iff (value : Word result) :
    let native := ∃ budget, runSource p input budget = some value
    ((∃ budget, outcome.runCF input budget = some value) ↔ native) ∧
      ((∃ budget, outcome.runNumbered input budget = some value) ↔ native)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total
