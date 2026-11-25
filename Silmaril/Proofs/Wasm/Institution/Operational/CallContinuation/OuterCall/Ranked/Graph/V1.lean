module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.NativeCommon
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (AdminInstr Frame FuncAddr Value)
open Computed

private theorem expression_code (fn : Function) :
    expression fn.v1Func.body = (Body.running fn.initial fn.code).render v1Admin := by
  change expression (fn.instructions Sequence.v1Source .unreachable) = _
  rw [Function.instructions, expression_append]
  change (fn.initial.map Sequence.v1Source.value).map AdminInstr.source ++
      (fn.code.map (Op.emit Sequence.v1Source .unreachable)).map AdminInstr.source =
    values fn.initial ++ fn.code.map v1Admin.emit
  rw [List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro v _
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  · apply List.map_congr_left
    intro op _
    cases op with
    | numeric op => cases op <;> rfl
    | call | unreachable => rfl

private theorem lift_label {H : Type} {s : Store H} {caller parent : Frame} {n : Nat}
    {before after : List Admin} (move : Step CallFrame.v1NoHost ⟨s, parent, before⟩ ⟨s, parent, after⟩) :
    Step CallFrame.v1NoHost ⟨s, caller, [.frame n parent [.label n [] before]]⟩
      ⟨s, caller, [.frame n parent [.label n [] after]]⟩ :=
  .frame (.label move n []) n caller

theorem sound {H : Type} {s : Store H} {program : Program} (checked : program.checkV1 = true)
    (allocated : program.V1Allocated s) (address : FuncAddr) :
    ∀ {caller target fn a b}, target.address = address →
      Root program caller target fn → Admitted program fn a →
      program.Edge ((Bool.and_eq_true_iff.mp checked).1) address a b →
      Step CallFrame.v1NoHost (v1Config s caller target a) (v1Config s caller target b) := by
  have check : program.check = true := (Bool.and_eq_true_iff.mp checked).1
  induction address using (program.table.wellFounded (Program.rankCheck check)).induction with
  | h address ih =>
    intro caller target fn a b addr root ready move
    subst address
    cases (program.edge_iff check root.found).mp move with
    | resolve args =>
      simpa only [v1Config, Phase.render, v1Admin, v1Syntax, Function.comp_def, List.append_nil] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s caller _ _ root.resolves) args []
    | enter args typed =>
      have arity : args.length = fn.declaration.type.params.length :=
        (List.length_map ..).symm.trans (congrArg List.length typed)
      have step := Step.invokeWasm (host := CallFrame.v1NoHost) s caller target.address
        fn.declaration.type fn.declaration.module fn.v1Func args (allocated _ _ root.found)
        arity (program.scalar_result checked root.found)
      rw [expression_code] at step
      simpa only [v1Config, Phase.render, v1Admin, ← root.declared, Declaration.type, Declaration.frame, Function.v1Func] using step
    | @numeric args stack op rest answer reduce =>
      rw [root.declared] at reduce
      apply lift_label
      exact (Prefix.v1_step_iff (s := s) (f := target.declaration.frame args) (stack := stack) (op := op)
        (tail := rest.map v1Admin.emit)).mpr ⟨answer, reduce, by cases answer <;> rfl⟩
    | unreachable args stack rest =>
      apply lift_label
      change Step CallFrame.v1NoHost
        ⟨s, target.declaration.frame args, values stack ++ .source .unreachable :: rest.map v1Admin.emit⟩
        ⟨s, target.declaration.frame args, values stack ++ .trap :: rest.map v1Admin.emit⟩
      simpa only [List.append_assoc, List.singleton_append] using
        Step.context (Step.pure (host := CallFrame.v1NoHost) s (target.declaration.frame args) PureStep.unreachable)
          stack (rest.map v1Admin.emit)
    | dispatch args saved operands child rest used count =>
      obtain ⟨_, _, _, resolves⟩ := program.linked_target check root.found used
      have found : child.Resolves (target.declaration.frame args) := by
        simpa only [CallTarget.Resolves, Declaration.frame, ← root.declared] using resolves
      apply lift_label
      simpa only [Body.render, Phase.render, v1Admin, Syntax.emit, Op.emit, v1Syntax, Function.comp_def,
        values_append, List.map_cons, List.append_assoc, List.singleton_append] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s (target.declaration.frame args)
          child.index child.address found) (saved ++ operands) (rest.map v1Admin.emit)
    | child args saved child rest used live step =>
      cases ready with
      | active _ _ childFound declared _ childReady _ =>
        obtain ⟨_, _, _, resolves⟩ := program.linked_target check root.found used
        have childResolves : child.Resolves (target.declaration.frame args) := by
          simpa only [CallTarget.Resolves, Declaration.frame, ← root.declared] using resolves
        have inside := ih child.address (program.target_resolved check root.found used)
          rfl ⟨childFound, declared, childResolves⟩ childReady step
        apply lift_label
        rw [render_attach (ops := v1Admin) values_append]
        exact Step.context inside saved (rest.map v1Admin.emit)
    | discard cut =>
      exact lift_label ((Prefix.v1_discard_iff v1Admin.emit).mpr ⟨_, _, cut, rfl⟩)
    | leaveValues args stack =>
      simpa only [v1Config, Phase.render, Body.render, v1Admin, List.map_nil, List.append_nil, Nested.resultCode] using
        Step.frame (Step.pure (host := CallFrame.v1NoHost) s (target.declaration.frame args)
          (.labelDone target.declaration.results.length [] stack)) target.declaration.results.length caller
    | leaveTrap => exact .frame (.pure s _ (.labelTrap _ [])) _ caller
    | leaveFrame args result resultTyped =>
      cases result with
      | trap => exact .pure s caller (.frameTrap _ _)
      | values xs =>
        exact .pure s caller (.frameDone _ _ xs ((result_length resultTyped).trans
          (congrArg (fun decl => decl.results.length) root.declared)))

private theorem function_to_lime (fn : Function) : fn.v1Func.toLime = fn.limeFunc := by
  have body : Wasm.V1.Expr.toLime (fn.instructions Sequence.v1Source .unreachable) =
      fn.instructions Sequence.limeSource .unreachable := by
    rw [Wasm.V1.Expr.toLime_eq_map, Function.instructions, Function.instructions, List.map_append,
      List.map_map, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro v _
      rcases v with ⟨t, bits⟩
      cases t <;> rfl
    · apply List.map_congr_left
      intro op _
      cases op with
      | numeric op => cases op <;> rfl
      | call | unreachable => rfl
  exact congrArg (fun code => (⟨fn.declaration.typeIndex, fn.declaration.locals, code⟩ : Wasm.Lime1.Func)) body

theorem allocations_to_lime {H : Type} {s : Store H} {program : Program} (allocated : program.V1Allocated s) :
    program.LimeAllocated (s.mapCode Wasm.V1.Func.toLime) := by
  intro address fn found
  rw [Execution.Runtime.Store.mapCode_funcs_getElem?, allocated address fn found]
  simp [Execution.Runtime.FuncInst.mapCode, function_to_lime]

private theorem rest_to_lime (rest : List Op) :
    codeToLime (rest.map v1Admin.emit) = rest.map limeAdmin.emit := by
  change AdminInstr.mapList Wasm.V1.Instr.toLime (rest.map v1Admin.emit) = _
  rw [AdminInstr.mapList_eq_map, List.map_map]
  apply List.map_congr_left
  intro op _
  cases op with
  | numeric op => cases op <;> rfl
  | call | unreachable => rfl

mutual

private theorem phase_to_lime (target : CallTarget) (q : Phase) :
    codeToLime (q.render v1Admin target) = q.render limeAdmin target := by
  cases q with
  | call args | invoke args =>
    simp only [Phase.render, codeToLime_append, v1Admin, limeAdmin, map_values]
    rfl
  | label args body =>
    change [AdminInstr.frame target.declaration.results.length (target.declaration.frame args)
      [.label target.declaration.results.length [] (codeToLime (body.render v1Admin))]] = _
    rw [body_to_lime body]
    rfl
  | exit args result =>
    change [AdminInstr.frame target.declaration.results.length (target.declaration.frame args)
      (codeToLime (Nested.resultCode values .trap result))] = _
    cases result with
    | trap => rfl
    | values stack =>
      change [AdminInstr.frame target.declaration.results.length (target.declaration.frame args)
        (codeToLime (values stack))] = _
      rw [map_values]
      rfl
  | done result =>
    cases result with
    | trap => rfl
    | values stack => exact map_values stack

private theorem body_to_lime (q : Body) :
    codeToLime (q.render v1Admin) = q.render limeAdmin := by
  cases q with
  | running stack rest =>
    change codeToLime (values stack ++ rest.map v1Admin.emit) = _
    rw [codeToLime_append, map_values, rest_to_lime]
    rfl
  | active saved target child rest =>
    change codeToLime (values saved ++ child.render v1Admin target ++ rest.map v1Admin.emit) = _
    simp only [codeToLime_append, map_values, rest_to_lime, phase_to_lime target child]
    rfl
  | trapped saved rest =>
    change codeToLime (values saved ++ .trap :: rest.map v1Admin.emit) = _
    rw [codeToLime_append, map_values, codeToLime_cons, rest_to_lime]
    rfl

end

theorem config_to_lime {H : Type} (s : Store H) (caller : Frame) (target : CallTarget) (q : Phase) :
    (v1Config s caller target q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller target q := by
  change (⟨_, _, codeToLime (q.render v1Admin target)⟩ : Wasm.Lime1.Execution.Config H) = _
  rw [phase_to_lime]
  rfl

theorem reflect_lime_step {H : Type} {s : Store H} {program : Program} (checked : program.checkV1 = true)
    (allocated : program.V1Allocated s) {caller target fn a dst}
    (root : Root program caller target fn) (ready : Admitted program fn a)
    (step : Wasm.Lime1.Execution.Step CallFrame.limeNoHost (v1Config s caller target a).toLime dst) :
    ∃ mid, Step CallFrame.v1NoHost (v1Config s caller target a) mid ∧ mid.toLime = dst := by
  rw [config_to_lime] at step
  obtain ⟨out, move, rfl⟩ := (Lime1.step_iff (Bool.and_eq_true_iff.mp checked).1
    (allocations_to_lime allocated) target.address rfl root ready).mp step
  exact ⟨_, sound checked allocated target.address rfl root ready move, config_to_lime s caller target out⟩

theorem step_iff {H : Type} {s : Store H} {program : Program} (checked : program.checkV1 = true)
    (allocated : program.V1Allocated s) {caller target fn a dst}
    (root : Root program caller target fn) (ready : Admitted program fn a) :
    Step CallFrame.v1NoHost (v1Config s caller target a) dst ↔
      ∃ out, program.Edge ((Bool.and_eq_true_iff.mp checked).1) target.address a out ∧ dst = v1Config s caller target out := by
  constructor
  · intro step
    have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    rw [config_to_lime] at mapped
    obtain ⟨out, move, eq⟩ := (Lime1.step_iff (Bool.and_eq_true_iff.mp checked).1
      (allocations_to_lime allocated) target.address rfl root ready).mp mapped
    exact ⟨out, move, CallContinuation.config_toLime_injective H (eq.trans (config_to_lime s caller target out).symm)⟩
  · rintro ⟨out, move, rfl⟩
    exact sound checked allocated target.address rfl root ready move

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.V1
