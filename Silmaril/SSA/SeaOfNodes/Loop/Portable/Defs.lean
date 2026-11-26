module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Denotation
public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs

/-! Common observations for the three lowerings of the concrete single-latch profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Portable

open Diamond (Val)
open Diamond.LambdaSSA (Atom inputEnv instruction)
open RVSDG (Tuple)
open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ : List Width} {carried result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable (g : Loop.MLIR.CF.Program Γ carried result entrySigs headerSigs) (input : Env Γ)

/-- Actual finite evaluation of the emitted λSSA CFG, with unit ambient state. -/
abbrev LambdaEval (label : Nat) (payload : Value (Atom Loop.MLIR.CF.model)) : Prop :=
  Semantics.Region.Eval (instruction Loop.MLIR.CF.model)
    (inputEnv Loop.MLIR.CF.model (sourceInputs input)) (LambdaSSA.Generic.lower g) () label payload ()

/-- Actual partial observation of the numbered θ graph in the induced runtime. -/
noncomputable abbrev observeTheta :
    Part (Tuple (Val Word) [.value (.data result)]) :=
  RVSDG.NestedTheta.Partial.observe (RVSDG.NestedTheta.MonadicModel.ofRuntime
    (thetaRuntime Loop.MLIR.CF.model)) g.lowerTheta (sourceInputs input)

/-- Actual partial observation of the embedded Basic CFG in the matched evaluator. -/
noncomputable abbrev observeCF : Part (Outcome [result]) :=
  (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (Loop.MLIR.CF.lower g)).denotePart
    Loop.MLIR.CF.evalOp input

/-- The source partial value determines every target's finite observation.
λSSA returns a packed payload at exit zero. The other targets package the
same partial value in their respective singleton result interfaces. -/
structure Agreement : Prop where
  lambda_eval_iff (label : Nat) (payload : Value (Atom Loop.MLIR.CF.model)) :
    LambdaEval g input label payload ↔
      ∃ value ∈ g.denote Loop.MLIR.CF.model (sourceInputs input),
        label = 0 ∧ payload = LambdaSSA.Generic.packResult Loop.MLIR.CF.model value
  theta :
    observeTheta g input =
      (g.denote Loop.MLIR.CF.model (sourceInputs input)).map (fun value => .cons value .nil)
  cf :
    observeCF g input =
      (g.denote Loop.MLIR.CF.model (sourceInputs input)).map (fun value => .returned (.cons value .nil))

end Silmaril.SSA.SeaOfNodes.Loop.Portable
