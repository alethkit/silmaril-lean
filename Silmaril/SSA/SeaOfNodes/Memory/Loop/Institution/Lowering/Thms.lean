module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Adequacy

/-! Preserve and reflect finite returns of the emitted λSSA and θ programs. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering

open CategoryTheory
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.LambdaSSA (Atom packet)
open Isotope (Value)

variable {P Q : EntrySignature}

/-- Every finite CFG execution returns the packed word at exit zero with
exactly a whole heap observed by the native loop. -/
theorem lambda_observation_iff (graph : Graph P.args) (model : EntryModel P)
    (initial final : Heap model.cells) (label : Nat) (payload : Value (Atom model.cells)) :
    lambdaReturns (lowerLambda graph) model initial label payload final ↔
      ∃ word, (word, final) ∈ graph.denote model.input initial ∧ label = 0 ∧ payload = packet word :=
  Proofs.lambda_observation_iff graph model initial final label payload

theorem theta_observation_iff (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    thetaObservation graph model initial = Part.some (encodeResult word final) ↔
      (word, final) ∈ graph.denote model.input initial :=
  Proofs.theta_observation_iff graph model initial word final

/-- The existing numbered partial observation is the encoded native partial
word and heap. This includes absence of any finite return. -/
theorem theta_observation (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    thetaObservation graph model initial =
      (graph.denote model.input initial).map (fun result => encodeResult result.1 result.2) :=
  Proofs.theta_observation graph model initial

theorem lambda_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ label payload final, ¬ lambdaReturns (lowerLambda graph) model initial label payload final) ↔
      graph.denote model.input initial = Part.none :=
  Proofs.lambda_no_return_iff graph model initial

theorem theta_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    thetaObservation graph model initial = Part.none ↔ graph.denote model.input initial = Part.none :=
  Proofs.theta_no_return_iff graph model initial

/-- Equality of all finite λSSA observations preserves and reflects native satisfaction. -/
theorem lambda_satisfaction (e : Equation P) (model : EntryModel P) :
    lambdaHolds e model ↔ e.Holds model :=
  Proofs.lambda_satisfaction e model

theorem theta_satisfaction (e : Equation P) (model : EntryModel P) :
    thetaHolds e model ↔ e.Holds model :=
  Proofs.theta_satisfaction e model

theorem lambda_satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    lambdaHolds (e.map h) model ↔ lambdaHolds e (reduct h model) :=
  (lambda_satisfaction (e.map h) model).trans
    ((e.satisfaction h model).trans (lambda_satisfaction e (reduct h model)).symm)

theorem theta_satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    thetaHolds (e.map h) model ↔ thetaHolds e (reduct h model) :=
  (theta_satisfaction (e.map h) model).trans
    ((e.satisfaction h model).trans (theta_satisfaction e (reduct h model)).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering
