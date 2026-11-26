module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution.Proofs

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → NativeSignature, Model → NativeModel, Equation → NativeEquation
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution (mapGraph reduct observe_mapGraph)
open Isotope (Value)
open Isotope.Institution.Observational
  (Observation ssaBeh ret_mem_ssaBeh fault_mem_ssaBeh diverge_mem_ssaBeh scoped_eval_congr)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open Isotope.Morphism.SSAIter (ScopedRegion envOfBound_agrees)

variable {P Q : NativeSignature}

theorem ret_mem_eval (m : NativeModel P) (guard : Bool)
    (region : ScopedRegion Opcode 1 (entryContext P.args).length)
    (initial final : Heap m.cells) (label : Nat) (payload : Value (Atom m.cells)) :
    Observation.ret initial (label, payload) final ∈ ssaBeh 1 (entryModel m guard) region ↔
      Eval (Instruction m.cells) (entryEnv guard m.input) region.val initial label payload final :=
  ret_mem_ssaBeh.trans (scoped_eval_congr region.property
    (envOfBound_agrees (entryModel m guard).bound) (fun _ => rfl))

theorem ret_mem_returns (graph : Graph P.args) (m : NativeModel P) (guard : Bool)
    (initial : Heap m.cells) (word : Word) (final : Heap m.cells) :
    returnObservation initial (word, final) ∈ ssaBeh 1 (entryModel m guard) (scope graph) ↔
      graph.Returns guard m.input initial word final :=
  (ret_mem_eval m guard (scope graph) initial final 0 (packet word)).trans
    (returns_iff graph guard m.input initial word final).symm

private theorem fault_absent (graph : Graph P.args) (m : NativeModel P) (guard : Bool)
    (initial final : Heap m.cells) :
    Observation.fault initial final ∉ ssaBeh 1 (entryModel m guard) (scope graph) :=
  fun member => (fault_mem_ssaBeh.mp member).false

private theorem divergence_absent (graph : Graph P.args) (m : NativeModel P) (guard : Bool)
    (initial : Heap m.cells) :
    Observation.diverge initial ∉ ssaBeh 1 (entryModel m guard) (scope graph) := by
  intro member
  let result := m.observe graph guard initial
  have observed := (ret_mem_returns graph m guard initial result.1 result.2).2
    ((m.returns_iff_observe graph guard initial result.1 result.2).2 rfl)
  exact (ret_mem_ssaBeh.mp observed).not_diverges instruction_deterministic
    (Isotope.LambdaSSA.Semantics.External.Diverges.false_iff.mp (diverge_mem_ssaBeh.mp member))

theorem behavior_eq_range (graph : Graph P.args) (m : NativeModel P) (guard : Bool) :
    ssaBeh 1 (entryModel m guard) (scope graph) =
      Set.range (fun initial => returnObservation initial (m.observe graph guard initial)) := by
  apply Observation.set_eq_iff.mpr
  refine ⟨?_, fun initial final => iff_of_false (fault_absent graph m guard initial final)
    (by rintro ⟨_, equal⟩; cases equal),
    fun initial => iff_of_false (divergence_absent graph m guard initial)
      (by rintro ⟨_, equal⟩; cases equal)⟩
  rintro initial ⟨label, payload⟩ final
  refine (ret_mem_eval m guard (scope graph) initial final label payload).trans
    ((lower_eval_iff graph guard m.input initial final label payload).trans ?_)
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨initial, rfl⟩
  · rintro ⟨heap, observed⟩
    obtain ⟨rfl, result, state⟩ := Observation.ret.inj observed
    exact ⟨(congrArg Prod.fst result).symm, (congrArg Prod.snd result).symm, state.symm⟩

theorem room_satisfaction_at (e : NativeEquation P) (m : NativeModel P) (guard : Bool) :
    (room P).Sat (Discrete.mk (entryModel m guard)) (translateEquation e) ↔
      ∀ initial, m.observe e.lhs guard initial = m.observe e.rhs guard initial := by
  change ssaBeh 1 (entryModel m guard) (scope e.lhs) =
    ssaBeh 1 (entryModel m guard) (scope e.rhs) ↔ _
  constructor
  · intro equal initial
    let result := m.observe e.lhs guard initial
    have observed := (ret_mem_returns e.lhs m guard initial result.1 result.2).2
      ((m.returns_iff_observe e.lhs guard initial result.1 result.2).2 rfl)
    have run := (ret_mem_returns e.rhs m guard initial result.1 result.2).1 (equal ▸ observed)
    exact ((m.returns_iff_observe e.rhs guard initial result.1 result.2).1 run).symm
  · intro equal
    rw [behavior_eq_range, behavior_eq_range]
    exact congrArg Set.range (funext fun initial => congrArg (returnObservation initial) (equal initial))

theorem behavior_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (m : NativeModel Q) (guard : Bool) :
    ssaBeh 1 (entryModel m guard) (scope (mapGraph h graph)) =
      ssaBeh 1 (entryModel (reduct h m) guard) (scope graph) :=
  (behavior_eq_range (mapGraph h graph) m guard).trans
    ((congrArg Set.range (funext fun initial =>
      congrArg (returnObservation initial) (observe_mapGraph h m graph guard initial))).trans
      (behavior_eq_range graph (reduct h m) guard).symm)

theorem room_satisfaction_reindex (h : P ⟶ Q) (e : NativeEquation P) (m : NativeModel Q) (guard : Bool) :
    (room Q).Sat (Discrete.mk (entryModel m guard)) (translateEquation (e.map h)) ↔
      (room P).Sat (Discrete.mk (entryModel (reduct h m) guard)) (translateEquation e) := by
  have lhs := behavior_mapGraph h e.lhs m guard
  have rhs := behavior_mapGraph h e.rhs m guard
  exact ⟨fun equal => lhs.symm.trans (equal.trans rhs), fun equal => lhs.trans (equal.trans rhs.symm)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution.Proofs
