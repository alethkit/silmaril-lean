module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Defs
import Mathlib.Data.List.InsertIdx
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier (operations)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower)

variable {Input Γ Δ : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {first : AfterReorder.Plan} {consumerOrigin : Nat} {prepared : Prepared Input carried result}

private theorem savedOrigins_agree (value : BitVec saved.val) (old : BitVec carried.val)
    (input : Env Input) : CapturesAgree savedOrigins (.cons value (.cons old input)) (.cons value input) := by
  intro _ ref capture fromOrigin
  cases ref with
  | here => cases fromOrigin; rfl
  | there ref =>
    cases ref with
    | here => cases fromOrigin
    | there ref => cases fromOrigin; rfl

theorem findCandidate?_value {index cut : Nat}
    {origins : Origins (saved :: Input) Γ} {code : Block TargetOp (Label saved carried result) Γ [result]}
    {candidate : Candidate Input saved carried result}
    (found : findCandidate? index cut origins code = some candidate)
    (env : Env Γ) (inputs : Env (saved :: Input)) (agree : CapturesAgree origins env inputs) :
    valueAt? index code env = some ⟨candidate.width, evalOp candidate.op (candidate.inputs.eval inputs)⟩ := by
  induction code generalizing index cut with
  | terminator => simp [findCandidate?] at found
  | letOp op operands rest ih =>
    cases index with
    | zero =>
      cases capture : captureOrigins? origins operands with
      | none => simp [findCandidate?, capture] at found
      | some captured =>
        by_cases empty : positions 0 captured 0 = []
        · simp [findCandidate?, capture, empty] at found
        · simp [findCandidate?, capture, empty] at found
          subst candidate
          simp only [valueAt?, evalCaptureOrigins origins operands capture env inputs agree]
    | succ index =>
      apply ih found (.cons (evalOp op (operands.eval env)) env)
      intro _ ref captured fromOrigin
      cases ref with
      | here => cases fromOrigin
      | there ref => exact agree ref captured fromOrigin

private theorem routeCode_operations (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (rename : Rename Γ Δ) (kept : Operands Δ [saved]) :
    operations (routeCodeWith (saved := saved) (extra := []) rename kept code) = operations code := by
  induction code generalizing Δ with
  | terminator => rfl
  | letOp _ _ _ ih => simp only [routeCodeWith, operations, ih]

private theorem rewrite_operations {index cut : Nat} {origins : Origins Input Γ}
    {code : Block TargetOp (SourceLabel carried result) Γ [result]}
    {binding : Binding Input Γ saved carried result}
    (found : findBinding index cut origins code = some ⟨saved, binding⟩)
    (rename : Rename Γ Δ) (keep : Var Δ saved) :
    operations (binding.rewrite rename keep) = (operations code).eraseIdx index := by
  induction code generalizing index cut Δ with
  | terminator => simp [findBinding] at found
  | letOp op operands rest ih =>
    cases index with
    | zero =>
      cases found
      exact routeCode_operations rest (replaceBinding rename keep) (.cons keep .nil)
    | succ index =>
      simp only [findBinding, Option.map_eq_some_iff] at found
      obtain ⟨⟨_, inner⟩, selected, eq⟩ := found
      cases eq
      simp only [Binding.prepend, operations, List.eraseIdx_cons_succ,
        ih selected (under rename) (.there keep)]

private theorem prepare?_spec (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (state : State Input carried result) (firstIndex : Nat) (cut : Point (SourceLabel carried result)),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      Header.Priority.resolve? state first.hoistOrigin = some firstIndex ∧
      hoistCodeWith? state.cfg.entry (state.cfg.block .header) firstIndex (chooseCfgCut? state.cfg) =
        some (cut, prepared.intermediate) ∧
      prepared.origins = state.origins.eraseIdx firstIndex ∧
      prepared.origins.idxOf? consumerOrigin = some prepared.index ∧
      findCandidate? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
        some prepared.consumer ∧
      checkConsumer prepared.intermediate.2 prepared.consumer = true := by
  obtain ⟨state, ran, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨firstIndex, resolved, next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨⟨cut, intermediate⟩, moved, next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨index, located, next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨consumer, found, next⟩ := Option.bind_eq_some_iff.mp next
  cases checked : checkConsumer intermediate.2 consumer with
  | false => simp [checked] at next
  | true =>
    simp [checked] at next
    subst prepared
    exact ⟨state, firstIndex, cut, ran, resolved, moved, rfl, located, found, checked⟩

theorem prepare?_replay_first (accepted : prepare? g first consumerOrigin = some prepared) :
    AfterReorder.replay? g first = some prepared.intermediate := by
  obtain ⟨_, _, _, ran, resolved, moved, _⟩ := prepare?_spec accepted
  simp [AfterReorder.replay?, AfterReorder.finish?, ran, resolved, moved]

theorem prepare?_placement (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (state : State Input carried result) (firstIndex : Nat),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      state.origins[firstIndex]? = some first.hoistOrigin ∧
      prepared.origins = state.origins.eraseIdx firstIndex ∧
      prepared.origins[prepared.index]? = some consumerOrigin ∧
      prepared.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
        (operations (prepared.intermediate.2.block .header)).map some ∧
      findCandidate? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
        some prepared.consumer ∧
      Legal prepared.intermediate.2 prepared.consumer.operands prepared.consumer.uses ⟨none, 1⟩ := by
  obtain ⟨state, firstIndex, _, ran, resolved, moved, erased, located, foundConsumer, checked⟩ := prepare?_spec accepted
  have tracked := Header.Sequence.run?_tracked (Header.Sequence.initial_tracked (lower g)) ran
  have secondAt : prepared.origins[prepared.index]? = some consumerOrigin := by
    obtain ⟨bound, eq, _⟩ := List.idxOf?_eq_some_iff.mp located
    exact List.getElem?_eq_some_iff.mpr ⟨bound, eq⟩
  obtain ⟨binding, found, _, _, _, _, code⟩ := hoistCodeWith?_spec moved
  have sameOrder : operations (prepared.intermediate.2.block .header) =
      (operations (state.cfg.block .header)).eraseIdx firstIndex := by
    rw [code]
    exact rewrite_operations found Var.there .here
  have aligned : prepared.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
      (operations (prepared.intermediate.2.block .header)).map some := by
    rw [erased, ← List.eraseIdx_map, tracked.2.1, List.eraseIdx_map, sameOrder]
  let _ : DecidableEq (Target (Label prepared.intermediate.1 carried result)) := targetDecEq
  exact ⟨state, firstIndex, ran, Header.Priority.resolve?_sound resolved, erased, secondAt,
    aligned, foundConsumer, (Dominance.Placement.checkCut_iff.mp checked).2⟩

theorem prepare?_available (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      ∀ (input : Env Input) (old : BitVec carried.val),
        let saved := evalOp producer (operands.eval input)
        valueAt? prepared.index (prepared.intermediate.2.block .header) (.cons saved (.cons old input)) =
          some ⟨prepared.consumer.width, evalOp prepared.consumer.op
            (prepared.consumer.inputs.eval (.cons saved input))⟩ := by
  obtain ⟨state, _, _, _, _, moved, _, _, found, _⟩ := prepare?_spec accepted
  obtain ⟨binding, _, _, _, operands, _, code⟩ := hoistCodeWith?_spec moved
  refine ⟨binding.args, binding.op, operands, routeCode Var.there .here state.cfg.entry, ?_, ?_⟩
  · rw [code]
    rfl
  · intro input old
    exact findCandidate?_value found _ _ (savedOrigins_agree _ old input)

theorem prepare?_first_routes (accepted : prepare? g first consumerOrigin = some prepared)
    (input : Env Input) :
    ∃ (source : Cfg TargetOp (SourceLabel carried result) Input [result])
      (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      prepared.intermediate.2.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      Routes source prepared.intermediate.2 input (evalOp producer (operands.eval input)) := by
  obtain ⟨state, _, _, ran, _, moved, _⟩ := prepare?_spec accepted
  obtain ⟨binding, found, _, _, operands, captured, code⟩ := hoistCodeWith?_spec moved
  obtain ⟨_, headerOnly, _⟩ := Header.Sequence.run?_header ran
  have exit : state.cfg.block .exit = .terminator (.ret (.cons .here .nil)) := by
    rw [headerOnly]
    rfl
  refine ⟨state.cfg, binding.args, binding.op, operands, routeCode Var.there .here state.cfg.entry,
    ?_, ?_, ?_⟩
  · rw [code]
    rfl
  · rw [code]
    rfl
  · rw [code]
    exact emitHeader_routes exit binding found operands captured input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
