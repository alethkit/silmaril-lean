module

public import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Loops.Proofs

open Execution.Runtime (Value AdminInstr)
open CallContinuation

section Core

open Execution.Core
open Wasm.SingleThreaded.Det (noHost)

theorem core_loop_step_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame}
    {bt : BlockType} {body : List Instr} {stack : List Val} {rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals stack ++ .plain (.loop bt body) :: rest⟩ dst ↔
      ∃ (saved args : List Val) (params results : List Wasm.Validation.CValType),
        stack = saved ++ args ∧ f.module.blockType? bt = some (params, results) ∧
        args.length = params.length ∧
        dst = ⟨s, f, vals saved ++ .label params.length [.loop bt body] (vals args ++ expression body) :: rest⟩ := by
  constructor
  · rcases dst with ⟨s', f', code⟩
    intro step
    rcases Sim.Step.split_head (a := .plain (.loop bt body)) rfl step with
      ⟨outside, used, _, split, head, rfl⟩ | ⟨bad, _⟩ | ⟨bad, _⟩
    · obtain ⟨kept, args, params, results, eq, lookup, count, target⟩ := head.loop_vals_inv
      cases target
      exact ⟨outside ++ kept, args, params, results, by rw [split, eq, List.append_assoc],
        lookup, count, by simp only [vals_append, List.append_assoc, List.singleton_append]⟩
    · cases bad
    · cases bad
  · rintro ⟨saved, args, params, results, rfl, lookup, count, rfl⟩
    simpa only [vals_append, List.append_assoc, List.singleton_append] using
      Sim.Step.vals_left (Sim.Step.append_right (Step.loop (P := P) (host := noHost) (s := s)
        (body := body) lookup count) rest) saved

theorem core_entry_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame} {result : Option NumType}
    {saved : List Val} {body : List Instr} {rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals saved ++ .plain (.loop (Blocks.coreType result) body) :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ .label 0 [.loop (Blocks.coreType result) body] (expression body) :: rest⟩ := by
  have lookup : f.module.blockType? (Blocks.coreType result) =
      some ([], result.toList.map (fun t => .num t)) := by
    cases result <;> rfl
  rw [core_loop_step_iff]
  constructor
  · rintro ⟨kept, used, params, results, split, found, count, rfl⟩
    rw [lookup] at found
    cases found
    have empty : used = [] := List.eq_nil_of_length_eq_zero count
    subst used
    simp [vals, split]
  · intro eq
    exact ⟨saved, [], _, _, (List.append_nil _).symm, lookup, rfl, eq⟩

theorem core_restart_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame} {cont : List Instr}
    {saved scratch : List Val} {pending rest : List Admin} {dst : Config H} :
    Step P noHost
      ⟨s, f, vals saved ++ .label 0 cont (vals scratch ++ .plain (.br ⟨0⟩) :: pending) :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ expression cont ++ rest⟩ := by
  constructor
  · intro move
    have contextual := Blocks.Context.core_label_cont_iff.mp move
    have exitExact {next : Config H}
        (h : Step P noHost ⟨s, f, [.label 0 cont (vals scratch ++ .plain (.br ⟨0⟩) :: pending)]⟩ next) :
        next = ⟨s, f, expression cont⟩ := by
      rcases BranchExit.core_label_br_cont_iff.mp h with ⟨_, payload, _, count, _, eq⟩ | ⟨bad, _⟩
      · have empty : payload = [] := List.eq_nil_of_length_eq_zero count
        simpa [vals, empty] using eq
      · exact (Nat.lt_irrefl 0 bad).elim
    let surround (c : Config H) : Config H := ⟨c.store, c.frame, vals saved ++ c.code ++ rest⟩
    rcases contextual with ⟨mid, step, rfl⟩ | ⟨out, pop, rfl⟩
    · have wrapped := (Blocks.Context.core_label_cont_iff (P := P) (s := s) (f := f) (n := 0) (cont := cont)
        (saved := []) (rest := [])
        (dst := ⟨mid.store, mid.frame, [.label 0 cont mid.code]⟩)).mpr
        (.inl ⟨mid, step, by simp [vals]⟩)
      simpa [surround] using congrArg surround (exitExact wrapped)
    · have wrapped := (Blocks.Context.core_label_cont_iff (P := P) (s := s) (f := f) (n := 0) (cont := cont)
        (saved := []) (rest := [])
        (dst := ⟨s, f, out⟩)).mpr
        (.inr ⟨out, pop, by simp [vals]⟩)
      exact congrArg surround (exitExact wrapped)
  · rintro rfl
    apply Blocks.Context.core_label_cont_iff.mpr
    refine .inr ⟨_, ?_, rfl⟩
    simpa [vals, List.append_assoc] using
      (LabelExit.brZero (cont := cont) (l := ⟨0⟩) (vs' := scratch) (vs := []) (rest := pending) rfl rfl)

theorem core_result_iff {H : Type} {P : Numerics.Profile} {s : Store H} {f : Frame} {cont : List Instr}
    {saved : List Val} {r : Nested.Result} {rest : List Admin} {dst : Config H} :
    let code := Nested.resultCode Blocks.Context.coreValues .trap r
    Step P noHost ⟨s, f, vals saved ++ .label 0 cont code :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ code ++ rest⟩ := by
  dsimp only
  rw [Blocks.Context.core_label_cont_iff]
  constructor
  · rintro (⟨_, inside, _⟩ | ⟨out, pop, rfl⟩)
    · exact (Nested.core_result_stuck inside).elim
    · rw [Nested.core_label_result pop]
  · rintro rfl
    cases r with
    | values stack => exact .inr ⟨_, .vals _, rfl⟩
    | trap => exact .inr ⟨_, .trap, rfl⟩

end Core

section Lime

open Wasm.Lime1.Execution
open Execution.Runtime (Frame)

theorem lime_entry_iff {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {saved : List Value} {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .source (.loop (Blocks.limeType result) body) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label 0 [.loop (Blocks.limeType result) body] (expression body) :: rest⟩ :=
  CallContinuation.OuterCall.Computed.lime_loop_iff

theorem lime_restart_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.Lime1.Expr}
    {saved scratch : List Value} {pending rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, f, values saved ++ .label 0 cont (values scratch ++ .source (.br ⟨0⟩) :: pending) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ expression cont ++ rest⟩ := by
  constructor
  · intro move
    have contextual := Blocks.Context.lime_label_cont_iff.mp move
    have exitExact {next : Config H}
        (h : Step CallFrame.limeNoHost ⟨s, f, [.label 0 cont (values scratch ++ .source (.br ⟨0⟩) :: pending)]⟩ next) :
        next = ⟨s, f, expression cont⟩ := by
      rcases BranchExit.lime_label_br_cont_iff.mp h with ⟨_, payload, _, count, _, eq⟩ | ⟨bad, _⟩
      · have empty : payload = [] := List.eq_nil_of_length_eq_zero count
        simpa [values, empty] using eq
      · exact (Nat.lt_irrefl 0 bad).elim
    let surround (c : Config H) : Config H := ⟨c.store, c.frame, values saved ++ c.code ++ rest⟩
    rcases contextual with ⟨mid, step, rfl⟩ | ⟨out, pop, rfl⟩
    · have wrapped := (Blocks.Context.lime_label_cont_iff (s := s) (f := f) (n := 0) (cont := cont)
        (saved := []) (rest := [])
        (dst := ⟨mid.store, mid.frame, [.label 0 cont mid.code]⟩)).mpr
        (.inl ⟨mid, step, by simp [values]⟩)
      simpa [surround] using congrArg surround (exitExact wrapped)
    · have wrapped := (Blocks.Context.lime_label_cont_iff (s := s) (f := f) (n := 0) (cont := cont)
        (saved := []) (rest := [])
        (dst := ⟨s, f, out⟩)).mpr
        (.inr ⟨out, pop, by simp [values]⟩)
      exact congrArg surround (exitExact wrapped)
  · rintro rfl
    apply Blocks.Context.lime_label_cont_iff.mpr
    refine .inr ⟨_, ?_, rfl⟩
    simpa [values, List.append_assoc] using
      (PureStep.labelBranch (types := f.module.types) 0 cont scratch [] pending rfl)

theorem lime_result_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.Lime1.Expr}
    {saved : List Value} {r : Nested.Result} {rest : List Admin} {dst : Config H} :
    let code := Nested.resultCode values .trap r
    Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label 0 cont code :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ code ++ rest⟩ := by
  dsimp only
  rw [Blocks.Context.lime_label_cont_iff]
  constructor
  · rintro (⟨_, inside, _⟩ | ⟨out, pop, rfl⟩)
    · exact (Nested.lime_result_stuck inside).elim
    · rw [Nested.lime_label_result pop]
  · rintro rfl
    cases r with
    | values stack => exact .inr ⟨_, .labelDone _ _ _, rfl⟩
    | trap => exact .inr ⟨_, .labelTrap _ _, rfl⟩

end Lime

section V1

open Wasm.V1.Execution
open Execution.Runtime (Frame)

theorem v1_entry_iff {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {saved : List Value} {body : Wasm.V1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .source (.loop result body) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label 0 [.loop result body] (expression body) :: rest⟩ := by
  constructor
  · intro move
    have lifted := move.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    have typeEq : Wasm.V1.BlockType.toLime result = Blocks.limeType result := by
      cases result <;> rfl
    have eq := (lime_entry_iff (dst := dst.toLime)).mp
      (by simpa [Config.toLime, AdminInstr.map, Wasm.V1.Instr.toLime, typeEq] using lifted)
    exact CallContinuation.config_toLime_injective H
      (by simpa [Config.toLime, AdminInstr.map, Wasm.V1.Instr.toLime, typeEq] using eq)
  · rintro rfl
    simpa only [List.append_assoc, List.singleton_append] using
      Step.context (Step.pure (host := CallFrame.v1NoHost) s f (PureStep.loop result body)) saved rest

theorem v1_restart_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.V1.Expr}
    {saved scratch : List Value} {pending rest : List Admin} {dst : Config H} :
    Step CallFrame.v1NoHost
      ⟨s, f, values saved ++ .label 0 cont (values scratch ++ .source (.br ⟨0⟩) :: pending) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ expression cont ++ rest⟩ := by
  constructor
  · intro move
    have lifted := move.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    have eq := (lime_restart_iff (dst := dst.toLime)).mp
      (by simpa [Config.toLime, AdminInstr.map, Wasm.V1.Instr.toLime] using lifted)
    exact CallContinuation.config_toLime_injective H
      (by simpa [Config.toLime, Wasm.V1.Expr.toLime_eq_map] using eq)
  · rintro rfl
    apply Blocks.Context.v1_label_cont_iff.mpr
    refine .inr ⟨_, ?_, rfl⟩
    simpa [values] using (PureStep.labelBranch 0 cont scratch [] pending rfl)

theorem v1_result_iff {H : Type} {s : Store H} {f : Frame} {cont : Wasm.V1.Expr}
    {saved : List Value} {r : Nested.Result} {rest : List Admin} {dst : Config H} :
    let code := Nested.resultCode values .trap r
    Step CallFrame.v1NoHost ⟨s, f, values saved ++ .label 0 cont code :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ code ++ rest⟩ := by
  dsimp only
  constructor
  · intro move
    have mapResult :
        codeToLime (Nested.resultCode values .trap r) =
          Nested.resultCode Wasm.Lime1.Execution.values .trap r := by
      cases r with
      | values stack => exact map_values stack
      | trap => rfl
    have lifted := move.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    have eq := (lime_result_iff (r := r) (dst := dst.toLime)).mp
      (by simpa only [Config.toLime, codeToLime_append, map_values, codeToLime_cons,
        AdminInstr.map, mapResult] using lifted)
    exact CallContinuation.config_toLime_injective H
      (by simpa only [Config.toLime, codeToLime_append, map_values, mapResult] using eq)
  · rintro rfl
    apply Blocks.Context.v1_label_cont_iff.mpr
    cases r with
    | values stack => exact .inr ⟨_, .labelDone _ _ stack, rfl⟩
    | trap => exact .inr ⟨_, .labelTrap _ _, rfl⟩

end V1

end Silmaril.Wasm.Institution.Operational.Loops.Proofs
