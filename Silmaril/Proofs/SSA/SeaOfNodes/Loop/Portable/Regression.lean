module

import Silmaril.SSA.SeaOfNodes.Loop.Portable.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.Portable

open Diamond (Val dataPorts)
open RVSDG (Tuple)
open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Env)
open Example (graph input width run)

private theorem lambdaTyped :
    (LambdaSSA.Generic.lower graph).HasType
      (LambdaSSA.Generic.inputContext (Loop.MLIR.CF.inputSorts [width, width, width]))
      [LambdaSSA.Generic.packed [.value (.data width)]] :=
  LambdaSSA.Generic.lower_hasType graph

-- A successful actual numbered run determines all three observations.
private theorem observesReturn (entry : Env [width, width, width]) (value : Word width)
    (fuel : Nat)
    (returned : graph.lowerTheta.run (thetaRuntime Loop.MLIR.CF.model) fuel (sourceInputs entry) =
      some (.cons value .nil)) :
    LambdaEval graph entry 0 (LambdaSSA.Generic.packResult Loop.MLIR.CF.model (out := .data width) value) ∧
      observeTheta graph entry = Part.some (.cons value .nil) ∧
      observeCF graph entry = Part.some (.returned (.cons value .nil)) := by
  have native := (graph.lowerTheta_returns_iff Loop.MLIR.CF.model (sourceInputs entry) value).mpr
    ⟨fuel, returned⟩
  have observed := (graph.returns_iff_mem_denote Loop.MLIR.CF.model (sourceInputs entry) value).mp native
  have sourceSome := Part.eq_some_iff.mpr observed
  have targets := agreement graph entry
  refine ⟨(targets.lambda_eval_iff 0 _).mpr ⟨value, observed, rfl, rfl⟩, ?_, ?_⟩
  · erw [targets.theta, sourceSome, Part.map_some]
  · erw [targets.cf, sourceSome, Part.map_some]

private theorem immediateExit :
    LambdaEval graph (input 5 5 1) 0 (LambdaSSA.Generic.packResult Loop.MLIR.CF.model
      (out := .data width) (10 : Word width)) ∧
      observeTheta graph (input 5 5 1) = Part.some (.cons (10 : Word width) .nil) ∧
      observeCF graph (input 5 5 1) = Part.some (.returned (.cons (10 : Word width) .nil)) :=
  observesReturn (input 5 5 1) 10 1 rfl

private theorem aboutToExit :
    LambdaEval graph (input 4 5 1) 0 (LambdaSSA.Generic.packResult Loop.MLIR.CF.model
      (out := .data width) (9 : Word width)) ∧
      observeTheta graph (input 4 5 1) = Part.some (.cons (9 : Word width) .nil) ∧
      observeCF graph (input 4 5 1) = Part.some (.returned (.cons (9 : Word width) .nil)) :=
  observesReturn (input 4 5 1) 9 2 rfl

private theorem repeatedBackedges :
    LambdaEval graph (input 2 5 1) 0 (LambdaSSA.Generic.packResult Loop.MLIR.CF.model
      (out := .data width) (7 : Word width)) ∧
      observeTheta graph (input 2 5 1) = Part.some (.cons (7 : Word width) .nil) ∧
      observeCF graph (input 2 5 1) = Part.some (.returned (.cons (7 : Word width) .nil)) :=
  observesReturn (input 2 5 1) 7 4 rfl

private theorem zeroBudget : run 0 5 5 1 = (some 10, some 10) := rfl
private theorem oneBackedgeBudget : run 1 4 5 1 = (some 9, some 9) := rfl
private theorem threeBackedgesBudget : run 3 2 5 1 = (some 7, some 7) := rfl
private theorem tooFewBackedges : run 2 2 5 1 = (none, none) := rfl
private theorem zeroStepAtFiniteBudget : run 3 2 5 0 = (none, none) := rfl

private theorem zeroStepUndefined :
    graph.denote Loop.MLIR.CF.model (sourceInputs (input 2 5 0)) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro result observed
  let old : Tuple (Val Word) (dataPorts [.data width]) := .cons (2 : Word width) .nil
  exact graph.not_returns_of_backedge_invariant Loop.MLIR.CF.model (sourceInputs (input 2 5 0)) result
    (· = old) rfl (fun _state same => same.symm ▸ ⟨old, rfl, rfl⟩)
    ((graph.returns_iff_mem_denote Loop.MLIR.CF.model (sourceInputs (input 2 5 0)) result).mpr observed)

private theorem zeroStepDiverges :
    (∀ label payload, ¬ LambdaEval graph (input 2 5 0) label payload) ∧
      observeTheta graph (input 2 5 0) = Part.none ∧
      observeCF graph (input 2 5 0) = Part.none := by
  have targets := agreement graph (input 2 5 0)
  constructor
  · intro label payload executed
    obtain ⟨value, member, _, _⟩ := (targets.lambda_eval_iff label payload).mp executed
    rw [zeroStepUndefined] at member
    exact Part.notMem_none value member
  · constructor
    · rw [targets.theta, zeroStepUndefined, Part.map_none]
    · rw [targets.cf, zeroStepUndefined, Part.map_none]

end Silmaril.SSA.SeaOfNodes.Loop.Portable
