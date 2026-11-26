module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Proofs

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.LambdaSSA (Atom packet)
open Isotope (Value)
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)

variable {P : EntrySignature}

theorem lambda_observation_iff (graph : Graph P.args) (model : EntryModel P)
    (initial final : Heap model.cells) (label : Nat) (payload : Value (Atom model.cells)) :
    lambdaReturns (lowerLambda graph) model initial label payload final ↔
      ∃ word, (word, final) ∈ graph.denote model.input initial ∧ label = 0 ∧ payload = packet word := by
  constructor
  · intro eval
    obtain ⟨count, word, returned, exit, value⟩ :=
      (LambdaSSA.lower_eval_iff graph model.input initial final label payload).1 eval
    exact ⟨word, (graph.returns_iff_mem_denote model.input initial word final).1 ⟨count, returned⟩,
      exit, value⟩
  · rintro ⟨word, member, rfl, rfl⟩
    have returned := (graph.returns_iff_mem_denote model.input initial word final).2 member
    obtain ⟨_, observed⟩ := (graph.returns_iff_portable model.input initial word final).1 returned
    exact observed.lambdaReturn

theorem theta_observation_iff (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    thetaObservation graph model initial = Part.some (encodeResult word final) ↔
      (word, final) ∈ graph.denote model.input initial := by
  have numbered := RVSDG.NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns
    (thetaRuntime model.cells) graph.lowerTheta (encodeInput initial model.input) (encodeResult word final)
  exact numbered.trans ((graph.lowerTheta_returns_iff model.input initial word final).symm.trans
    (graph.returns_iff_mem_denote model.input initial word final))

theorem theta_observation (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    thetaObservation graph model initial =
      (graph.denote model.input initial).map (fun result => encodeResult result.1 result.2) := by
  apply Part.ext
  intro output
  cases output with
  | cons word tail =>
    cases tail with
    | cons heap rest =>
      cases rest
      change encodeResult word heap ∈ thetaObservation graph model initial ↔ _
      refine Part.eq_some_iff.symm.trans ((theta_observation_iff graph model initial word heap).trans ?_)
      constructor
      · exact Part.mem_map _
      · intro encoded
        obtain ⟨result, member, equal⟩ := (Part.mem_map_iff _).1 encoded
        have observations : result = (word, heap) :=
          Prod.ext
            (congrArg (fun t : Tuple (WireVal model.cells) (Threaded wordPorts) => t.get .head) equal)
            (congrArg (fun t : Tuple (WireVal model.cells) (Threaded wordPorts) => t.get (.tail .head)) equal)
        exact observations ▸ member

theorem lambda_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ label payload final, ¬ lambdaReturns (lowerLambda graph) model initial label payload final) ↔
      graph.denote model.input initial = Part.none := by
  rw [Part.eq_none_iff]
  constructor
  · intro absent result member
    exact absent 0 (packet result.1) result.2
      ((lambda_observation_iff graph model initial result.2 0 (packet result.1)).2
        ⟨result.1, member, rfl, rfl⟩)
  · intro absent label payload final run
    obtain ⟨word, member, _, _⟩ := (lambda_observation_iff graph model initial final label payload).1 run
    exact absent (word, final) member

theorem theta_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    thetaObservation graph model initial = Part.none ↔ graph.denote model.input initial = Part.none := by
  rw [theta_observation, Part.eq_none_iff, Part.eq_none_iff]
  constructor
  · intro absent result member
    exact absent _ (Part.mem_map _ member)
  · intro absent _ encoded
    obtain ⟨result, member, _⟩ := (Part.mem_map_iff _).1 encoded
    exact absent result member

theorem lambda_satisfaction (e : Equation P) (model : EntryModel P) :
    lambdaHolds e model ↔ e.Holds model := by
  constructor
  · intro agree
    apply (e.holds_iff_returns model).2
    intro initial word final
    exact (LambdaSSA.returns_iff e.lhs model.input initial word final).trans
      ((agree initial 0 (packet word) final).trans
        (LambdaSSA.returns_iff e.rhs model.input initial word final).symm)
  · intro equal initial label payload final
    rw [lambda_observation_iff e.lhs model, lambda_observation_iff e.rhs model, equal initial]

theorem theta_satisfaction (e : Equation P) (model : EntryModel P) :
    thetaHolds e model ↔ e.Holds model := by
  constructor
  · intro equal initial
    apply Part.ext
    rintro ⟨word, final⟩
    rw [← theta_observation_iff e.lhs model initial word final,
      ← theta_observation_iff e.rhs model initial word final, equal initial]
  · intro equal initial
    rw [theta_observation e.lhs model initial, theta_observation e.rhs model initial, equal initial]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Proofs
