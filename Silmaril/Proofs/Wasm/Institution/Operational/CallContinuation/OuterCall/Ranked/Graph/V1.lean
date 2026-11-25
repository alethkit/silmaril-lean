module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.NativeCommon
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.V1Guard
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Typing
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.V1

open Wasm.V1.Execution
open Execution.Runtime (AdminInstr Frame FuncAddr Value)
open Computed

private theorem code_expression (code : List Op) :
    expression (Op.emitList v1CodeSyntax code) = code.map v1Admin.emit := by
  induction code with
  | nil => rfl
  | cons op rest ih =>
    change _ :: expression (Op.emitList v1CodeSyntax rest) = _ :: rest.map v1Admin.emit
    rw [ih]
    cases op with
    | numeric op => cases op <;> rfl
    | set | tee | call | block | indexedBlock | loop | if_ | br | brIf | brTable | return_ | unreachable => rfl

private theorem expression_code (fn : Function) :
    expression fn.v1Func.body = (Body.running fn.initial fn.code).render v1Admin := by
  change expression (fn.initial.map Sequence.v1Source.value ++ Op.emitList v1CodeSyntax fn.code) =
    values fn.initial ++ fn.code.map v1Admin.emit
  rw [show expression (fn.initial.map Sequence.v1Source.value ++ Op.emitList v1CodeSyntax fn.code) =
      expression (fn.initial.map Sequence.v1Source.value) ++ expression (Op.emitList v1CodeSyntax fn.code) from
    List.map_append .., code_expression]
  congr 1
  change (fn.initial.map Sequence.v1Source.value).map _ = _
  simp only [List.map_map, values]
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

private def regionConfig {H : Type} (s : Store H) (target : CallTarget) (n : Nat) :
    Phase → LabelKind → Config H
  | .label locals body, kind =>
    ⟨s, currentFrame target.declaration locals, [v1Admin.label n kind (body.render v1Admin)]⟩
  | .branching locals stack depth _, _ =>
    ⟨s, currentFrame target.declaration locals, values stack ++ [.source (.br depth)]⟩
  | .returning locals stack, _ =>
    ⟨s, currentFrame target.declaration locals, values stack ++ [.source .return_]⟩
  | .restart locals result original, _ =>
    ⟨s, currentFrame target.declaration locals, [v1Admin.emit (.loop result original)]⟩
  | .exit locals result, _ => ⟨s, currentFrame target.declaration locals, Nested.resultCode values .trap result⟩
  | _, _ => ⟨s, currentFrame target.declaration [], []⟩

private theorem lift_label {H : Type} {s : Store H} {parent parentNext : Frame}
    {n : Nat} {cont : Wasm.V1.Expr}
    {before after : List Admin} (move : Step CallFrame.v1NoHost ⟨s, parent, before⟩ ⟨s, parentNext, after⟩) :
    Step CallFrame.v1NoHost ⟨s, parent, [.label n cont before]⟩
      ⟨s, parentNext, [.label n cont after]⟩ :=
  .label move n cont

private theorem lift_nested {H : Type} {s : Store H} {target : CallTarget} {n : Nat}
    {kind innerKind : LabelKind} {locals saved : List Value} {result : Option NumType}
    {inner : Body} {rest : List Op} {next : Phase}
    (compatible : ∀ r original, innerKind = .loop r original → r = result)
    (shape : next.LabelOutcome)
    (move : Step CallFrame.v1NoHost
      (regionConfig s target (innerKind.results result).length (.label locals inner) innerKind)
      (regionConfig s target (innerKind.results result).length next innerKind)) :
    Step CallFrame.v1NoHost (regionConfig s target n (.label locals (inner.underLabel saved result rest innerKind)) kind)
      (regionConfig s target n (next.afterBlock saved result rest innerKind) kind) := by
  have wrapped := Step.label (Step.context move saved (rest.map v1Admin.emit))
    (kind.arity n) (kind.cont v1CodeSyntax)
  rw [regionConfig, render_under_label v1Admin saved result rest innerKind compatible]
  cases next with
  | call | invoke | done => cases shape
  | label ls body =>
    rw [Phase.afterBlock, regionConfig, render_under_label v1Admin saved result rest innerKind compatible]
    simpa only [regionConfig, v1Admin, List.append_assoc, List.singleton_append] using wrapped
  | branching | returning | restart =>
    simpa only [regionConfig, Phase.afterBlock, Body.render, List.map_cons, List.append_assoc,
      List.singleton_append, v1Admin, v1Emit, Op.emit, v1CodeSyntax, values_append] using wrapped
  | exit ls out =>
    cases out <;> simpa only [regionConfig, Phase.afterBlock, Body.render, Nested.resultCode,
      v1Admin, values_append, List.append_assoc, List.singleton_append] using wrapped

private theorem set_sound {H : Type} {s : Store H} {decl : Declaration}
    {locals next saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .set idx]⟩ ⟨next, []⟩) :
    Step CallFrame.v1NoHost ⟨s, currentFrame decl locals, (Body.running (saved ++ [v]) (.set idx :: rest)).render v1Admin⟩
      ⟨s, currentFrame decl next, (Body.running saved rest).render v1Admin⟩ := by
  have move := Locals.v1_sound (host := CallFrame.v1NoHost) (s := s) (m := decl.module) write
  have lifted := Step.context move saved (rest.map v1Admin.emit)
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.Codec.encode, Locals.v1Codec, Locals.legacyCodec,
    Locals.v1Instr, currentFrame, Body.render, v1Admin, v1Emit, Op.emit, v1CodeSyntax,
    List.append_assoc, values] at lifted ⊢ <;> exact lifted

private theorem tee_sound {H : Type} {s : Store H} {decl : Declaration}
    {locals saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .tee idx]⟩ ⟨locals, [.value v, .value v, .set idx]⟩) :
    Step CallFrame.v1NoHost ⟨s, currentFrame decl locals, (Body.running (saved ++ [v]) (.tee idx :: rest)).render v1Admin⟩
      ⟨s, currentFrame decl locals, (Body.running (saved ++ [v, v]) (.set idx :: rest)).render v1Admin⟩ := by
  have move := Locals.v1_sound (host := CallFrame.v1NoHost) (s := s) (m := decl.module) write
  have lifted := Step.context move saved (rest.map v1Admin.emit)
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.Codec.encode, Locals.v1Codec, Locals.legacyCodec,
    Locals.v1Instr, currentFrame, Body.render, v1Admin, v1Emit, Op.emit, v1CodeSyntax,
    List.append_assoc, values] at lifted ⊢ <;> exact lifted

private theorem region_sound {H : Type} {s : Store H} {program : Program} (check : program.check = true)
    {target : CallTarget} {fn : Function} (found : program.lookup target.address = some fn)
    (declared : fn.declaration = target.declaration)
    (descend : ∀ child ∈ fn.targets, ∀ {parent callee a b},
      Root program parent child callee → Admitted program callee a → a.supportsV1 = true → program.Edge check child.address a b →
      Step CallFrame.v1NoHost (v1Config s parent child a) (v1Config s parent child b))
    {a b : Phase} {kind : LabelKind} (edge : Layer fn (fun t => program.Edge check t.address) a b kind) :
    ∀ {fallthrough enclosing}, AdmittedAt program fn fallthrough enclosing a kind → (∃ ls body, a = .label ls body) →
      a.supportsV1 = true →
      Step CallFrame.v1NoHost (regionConfig s target fallthrough.length a kind) (regionConfig s target fallthrough.length b kind) := by
  induction edge <;> intro fallthrough enclosing ready isLabel supported
  all_goals
    let n := fallthrough.length
  case resolve => obtain ⟨_, _, impossible⟩ := isLabel; cases impossible
  case enter => obtain ⟨_, _, impossible⟩ := isLabel; cases impossible
  case leaveFrame => obtain ⟨_, _, impossible⟩ := isLabel; cases impossible
  case returnFrame => obtain ⟨_, _, impossible⟩ := isLabel; cases impossible
  case numeric locals stack op rest answer reduce =>
    apply lift_label
    exact (Prefix.v1_step_iff (s := s) (f := currentFrame target.declaration locals) (stack := stack) (op := op)
      (tail := rest.map v1Admin.emit)).mpr ⟨answer, reduce, by cases answer <;> rfl⟩
  case localSet write => exact lift_label (set_sound write)
  case localTee write => exact lift_label (tee_sound write)
  case ifSelect locals saved condition result thenBody elseBody rest =>
    apply lift_label
    let left := Op.emitList v1CodeSyntax thenBody
    let right := Op.emitList v1CodeSyntax elseBody
    have choose : PureStep [value (Value.int .i32 condition), .source (.if_ result left right)]
        [.source (.block result (if condition = 0 then right else left))] := by
      by_cases zero : condition = 0
      · rw [ite_eq_left zero]
        subst condition
        exact .ifZero result left right
      · rw [ite_eq_right zero]
        exact .ifNonzero result left right condition zero
    have move := Step.context (Step.pure (host := CallFrame.v1NoHost) s
      (currentFrame target.declaration locals) choose) saved (rest.map v1Admin.emit)
    simpa only [Body.render, v1Admin, v1Emit, Op.emit, v1CodeSyntax, Op.emitList_selected,
      List.map_cons, values, List.map_append, List.map_nil, List.append_assoc, List.cons_append, List.nil_append,
      left, right] using move
  case blockEnter locals saved result code rest =>
    apply lift_label
    have move := (Blocks.v1_entry_iff (host := CallFrame.v1NoHost) (s := s)
      (f := currentFrame target.declaration locals) (result := result) (body := Op.emitList v1CodeSyntax code)).mpr rfl
    rw [code_expression] at move
    simpa only [Body.render, List.map_cons, List.append_assoc, List.singleton_append,
      v1Admin, LabelKind.arity, LabelKind.cont, v1Emit, Op.emit, v1CodeSyntax, values, List.map_nil, List.nil_append] using
      Step.context move saved (rest.map v1Admin.emit)
  case blockStep locals saved result rest inner next step ih =>
    cases ready with
    | block ready _ => exact lift_nested (by simp) (label_outcome step ⟨_, _, rfl⟩) (ih ready ⟨_, _, rfl⟩ ((Bool.and_eq_true_iff.mp supported).1))
  case indexedBlockEnter =>
    simp [Phase.supportsV1, Body.supportsV1, codeV1, Op.supportsV1] at supported
  case indexedBlockStep =>
    contradiction
  case loopEnter locals saved result code rest =>
    apply lift_label
    exact (Loops.v1_entry_iff (result := result) (saved := saved) (body := Op.emitList v1CodeSyntax code)
      (rest := rest.map v1Admin.emit)).mpr (by rw [code_expression]; rfl)
  case loopStep locals inner next saved result original rest step ih =>
    cases ready with
    | loop ready _ _ =>
      exact lift_nested (fun _ _ eq => (LabelKind.loop.inj eq).1.symm)
        (label_outcome step ⟨_, _, rfl⟩) (ih ready ⟨_, _, rfl⟩ ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp supported).1).2))
  case unreachable locals stack rest =>
    apply lift_label
    change Step CallFrame.v1NoHost
      ⟨s, currentFrame target.declaration locals, values stack ++ .source .unreachable :: rest.map v1Admin.emit⟩
      ⟨s, currentFrame target.declaration locals, values stack ++ .trap :: rest.map v1Admin.emit⟩
    simpa only [List.append_assoc, List.singleton_append] using
      Step.context (Step.pure (host := CallFrame.v1NoHost) s (currentFrame target.declaration locals) PureStep.unreachable)
        stack (rest.map v1Admin.emit)
  case dispatch locals saved operands child rest used count =>
    obtain ⟨_, _, _, resolves⟩ := program.linked_target check found used
    have index : child.Resolves (currentFrame target.declaration locals) := by
      simpa only [CallTarget.Resolves, currentFrame, ← declared] using resolves
    apply lift_label
    simpa only [Body.render, Phase.render, Phase.renderAt, v1Admin, v1Emit, Op.emit, v1CodeSyntax, Sequence.v1Source, Function.comp_def,
      values_append, List.map_cons, List.append_assoc, List.singleton_append] using
      Step.context (Step.call (host := CallFrame.v1NoHost) s (currentFrame target.declaration locals)
        child.index child.address index) (saved ++ operands) (rest.map v1Admin.emit)
  case child locals saved child rest a b used live step =>
    cases ready with
    | active _ _ childFound childDeclared _ childReady _ =>
      obtain ⟨_, _, _, resolves⟩ := program.linked_target check found used
      have childResolves : child.Resolves (currentFrame target.declaration locals) := by
        simpa only [CallTarget.Resolves, currentFrame, ← declared] using resolves
      have inside := descend child used ⟨childFound, childDeclared, childResolves⟩ childReady (Bool.and_eq_true_iff.mp supported).1 step
      apply lift_label
      rw [render_attach (ops := v1Admin) values_append]
      exact Step.context inside saved (rest.map v1Admin.emit)
  case discard cut =>
    exact lift_label ((Prefix.v1_discard_iff v1Admin.emit).mpr ⟨_, _, cut, rfl⟩)
  case branchIf locals stack condition depth result rest =>
    apply lift_label
    have branch : PureStep [value (Value.int .i32 condition), .source (.brIf depth)]
        (if condition = 0 then [] else [.source (.br depth)]) := by
      by_cases zero : condition = 0
      · rw [ite_eq_left zero]
        subst condition
        exact .brIfZero depth
      · rw [ite_eq_right zero]
        exact .brIfNonzero depth condition zero
    have move := Step.context (Step.pure (host := CallFrame.v1NoHost) s
      (currentFrame target.declaration locals) branch) stack (rest.map v1Admin.emit)
    simpa only [Body.render, Op.map_br_if, v1Admin, v1Emit, Op.emit, v1CodeSyntax, values,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using move
  case branchTable locals stack selector depths fallback result rest =>
    apply lift_label
    have move := Step.context (Step.pure (host := CallFrame.v1NoHost) s
      (currentFrame target.declaration locals) (.brTable depths fallback selector)) stack (rest.map v1Admin.emit)
    simpa only [Body.render, v1Admin, v1Emit, Op.emit, v1CodeSyntax, values,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using move
  case branchHere kind locals extra payload result rest arity =>
    cases ready with
    | running _ typed =>
      have count : payload.length = kind.arity n :=
        arity.trans ((congrArg List.length (branch_here_result (checked_branch typed).1)).symm.trans
          (LabelKind.inputs_length kind fallthrough))
      have move := Step.pure (host := CallFrame.v1NoHost) s (currentFrame target.declaration locals)
        (PureStep.labelBranch (kind.arity n) (kind.cont v1CodeSyntax) extra payload (rest.map v1Admin.emit) count)
      cases kind with
      | exit | indexed =>
        simpa only [regionConfig, Body.render, v1Admin, LabelKind.branchHere, LabelKind.cont,
          v1Emit, Op.emit, v1CodeSyntax, List.map_cons, values_append, List.append_assoc, List.singleton_append, Nested.resultCode,
          expression, List.map_nil, List.append_nil, n] using move
      | loop result original =>
        have empty : payload = [] := List.eq_nil_of_length_eq_zero count
        subst payload
        simpa only [regionConfig, Body.render, v1Admin, LabelKind.branchHere, LabelKind.cont,
          v1Emit, Op.emit, v1CodeSyntax, expression, values, List.map_nil, List.nil_append,
          List.append_nil, List.map_cons, List.append_assoc, List.singleton_append, n] using move
  case branchOuter locals stack depth result rest outer =>
    have lowered : lowerLabel depth = lowerBranch depth := rfl
    simpa only [regionConfig, Body.render, v1Admin, v1Emit, Op.emit, v1CodeSyntax, List.map_cons,
      List.append_assoc, List.singleton_append, lowered, n] using
      Step.pure (host := CallFrame.v1NoHost) s (currentFrame target.declaration locals)
        (.labelBranchOuter (_ : Nat) (_ : Wasm.V1.Expr) stack (rest.map v1Admin.emit) depth (Nat.ne_of_gt outer))
  case returnLabel locals stack rest =>
    simpa only [regionConfig, Body.render, v1Admin, List.map_cons,
      v1Emit, Op.emit, v1CodeSyntax, List.append_assoc, List.singleton_append] using
      Step.pure (host := CallFrame.v1NoHost) s (currentFrame target.declaration locals)
        (.labelReturn (_ : Nat) (_ : Wasm.V1.Expr) stack (rest.map v1Admin.emit))
  case leaveValues locals stack =>
    simpa only [regionConfig, Body.render, v1Admin, List.map_nil, List.append_nil, Nested.resultCode] using
      Step.pure (host := CallFrame.v1NoHost) s (currentFrame target.declaration locals) (.labelDone (_ : Nat) (_ : Wasm.V1.Expr) stack)
  case leaveTrap => exact .pure s _ (.labelTrap _ _)

theorem sound {H : Type} {s : Store H} {program : Program} (checked : program.checkV1 = true)
    (allocated : program.V1Allocated s) (address : FuncAddr) :
    ∀ {caller target fn a b}, target.address = address →
      Root program caller target fn → Admitted program fn a → a.supportsV1 = true →
      program.Edge ((Bool.and_eq_true_iff.mp checked).1) address a b →
      Step CallFrame.v1NoHost (v1Config s caller target a) (v1Config s caller target b) := by
  have check : program.check = true := (Bool.and_eq_true_iff.mp checked).1
  induction address using (program.table.wellFounded (Program.rankCheck check)).induction with
  | h address ih =>
    intro caller target fn a b addr root ready supported move
    subst address
    have step := (program.edge_iff check root.found).mp move
    by_cases label : ∃ ls body, a = .label ls body
    · obtain ⟨ls, body, rfl⟩ := label
      have descend child (used : child ∈ fn.targets) {parent callee a b} (childRoot : Root program parent child callee)
          (childReady : Admitted program callee a) (ok : a.supportsV1 = true) (step : program.Edge check child.address a b) :=
        ih child.address (program.target_resolved check root.found used) rfl childRoot childReady ok step
      have localStep := region_sound check root.found root.declared descend step ready ⟨_, _, rfl⟩ supported
      rw [root.declared] at localStep
      have outcome := label_outcome step ⟨_, _, rfl⟩
      have lifted := Step.frame localStep target.declaration.results.length caller
      cases b with
      | branching =>
        have impossible := program.admitted_step check root.found ready move
        cases impossible with | branching _ found _ => simp at found
      | label | returning | exit => exact lifted
      | restart =>
        have impossible := program.admitted_step check root.found ready move
        cases impossible
      | call | invoke | done => cases outcome
    cases step with
    | resolve args =>
      simpa only [v1Config, Phase.render, Phase.renderAt, v1Admin, v1Syntax, Function.comp_def, List.append_nil] using
        Step.context (Step.call (host := CallFrame.v1NoHost) s caller _ _ root.resolves) args []
    | enter args typed =>
      have arity : args.length = fn.declaration.type.params.length :=
        (List.length_map ..).symm.trans (congrArg List.length typed)
      have step := Step.invokeWasm (host := CallFrame.v1NoHost) s caller target.address
        fn.declaration.type fn.declaration.module fn.v1Func args (allocated _ _ root.found)
        arity (program.scalar_result checked root.found)
      rw [expression_code] at step
      simpa only [v1Config, Phase.render, Phase.renderAt, v1Admin, LabelKind.arity, LabelKind.cont, ← root.declared, Declaration.type, Declaration.frame, Function.v1Func, currentFrame] using step
    | returnFrame locals extra results arity =>
      have n := arity.trans (congrArg (fun d => d.results.length) root.declared)
      simpa only [v1Config, Phase.render, Phase.renderAt, v1Admin, values_append, List.append_nil, Nested.resultCode] using
        Step.pure (host := CallFrame.v1NoHost) s caller
          (.frameReturn _ (currentFrame target.declaration locals) extra results [] n)
    | leaveFrame locals result resultTyped =>
      cases result with
      | trap => exact .pure s caller (.frameTrap _ _)
      | values xs =>
        exact .pure s caller (.frameDone _ _ xs ((result_length resultTyped).trans
          (congrArg (fun decl => decl.results.length) root.declared)))
    | _ => exact (label ⟨_, _, rfl⟩).elim

mutual

private theorem emit_to_lime (op : Op) (supported : op.supportsV1 = true) :
    (op.emit v1CodeSyntax).toLime = op.emit limeCodeSyntax := by
  cases op with
  | numeric op => cases op <;> rfl
  | set | tee | call | br | brIf | brTable | return_ | unreachable => rfl
  | indexedBlock => contradiction
  | block result code =>
    change Wasm.V1.Instr.toLime (.block result (Op.emitList v1CodeSyntax code)) =
      .block (Blocks.limeType result) (Op.emitList limeCodeSyntax code)
    rw [Wasm.V1.Instr.toLime, Wasm.V1.Expr.toLime_eq_map, emit_list_to_lime code supported]
    cases result <;> rfl
  | loop result code =>
    change Wasm.V1.Instr.toLime (.loop result (Op.emitList v1CodeSyntax code)) =
      .loop (Blocks.limeType result) (Op.emitList limeCodeSyntax code)
    rw [Wasm.V1.Instr.toLime, Wasm.V1.Expr.toLime_eq_map, emit_list_to_lime code supported]
    cases result <;> rfl
  | if_ result thenBody elseBody =>
    change Wasm.V1.Instr.toLime (.if_ result (Op.emitList v1CodeSyntax thenBody)
        (Op.emitList v1CodeSyntax elseBody)) =
      .if_ (Blocks.limeType result) (Op.emitList limeCodeSyntax thenBody) (Op.emitList limeCodeSyntax elseBody)
    obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp supported
    rw [Wasm.V1.Instr.toLime, Wasm.V1.Expr.toLime_eq_map, Wasm.V1.Expr.toLime_eq_map,
      emit_list_to_lime thenBody left, emit_list_to_lime elseBody right]
    cases result <;> rfl

private theorem emit_list_to_lime (code : List Op) (supported : codeV1 code = true) :
    (Op.emitList v1CodeSyntax code).map Wasm.V1.Instr.toLime = Op.emitList limeCodeSyntax code := by
  cases code with
  | nil => rfl
  | cons op rest =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp supported
    simp only [Op.emitList, List.map_cons, emit_to_lime op head, emit_list_to_lime rest tail]

end

private theorem function_to_lime (fn : Function) (supported : codeV1 fn.code = true) : fn.v1Func.toLime = fn.limeFunc := by
  have body : Wasm.V1.Expr.toLime (fn.instructions v1CodeSyntax) = fn.instructions limeCodeSyntax := by
    rw [Wasm.V1.Expr.toLime_eq_map, Function.instructions, Function.instructions, List.map_append, emit_list_to_lime fn.code supported]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro v _
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  exact congrArg (fun code => (⟨fn.declaration.typeIndex, fn.declaration.locals, code⟩ : Wasm.Lime1.Func)) body

theorem allocations_to_lime {H : Type} {s : Store H} {program : Program}
    (checked : program.checkV1 = true) (allocated : program.V1Allocated s) :
    program.LimeAllocated (s.mapCode Wasm.V1.Func.toLime) := by
  intro address fn found
  rw [Execution.Runtime.Store.mapCode_funcs_getElem?, allocated address fn found]
  simp [Execution.Runtime.FuncInst.mapCode, function_to_lime fn (checked_v1_function checked found).2]

private theorem rest_to_lime (rest : List Op) (supported : codeV1 rest = true) :
    codeToLime (rest.map v1Admin.emit) = rest.map limeAdmin.emit := by
  induction rest with
  | nil => rfl
  | cons op tail ih =>
    obtain ⟨head, suffix⟩ := Bool.and_eq_true_iff.mp supported
    have same : AdminInstr.map Wasm.V1.Instr.toLime (v1Admin.emit op) = limeAdmin.emit op := by
      cases op with
      | numeric op => cases op <;> rfl
      | _ => exact congrArg AdminInstr.source (emit_to_lime _ head)
    simp only [List.map_cons, codeToLime_cons, same, ih suffix]


mutual

private theorem phase_to_lime (target : CallTarget) (q : Phase) (supported : q.supportsV1 = true) :
    codeToLime (q.render v1Admin target) = q.render limeAdmin target := by
  cases q with
  | call args | invoke args =>
    simp only [Phase.render, Phase.renderAt, codeToLime_append, v1Admin, limeAdmin, map_values]
    rfl
  | label locals body =>
    change [AdminInstr.frame target.declaration.results.length (currentFrame target.declaration locals)
      [.label target.declaration.results.length [] (codeToLime (body.render v1Admin))]] = _
    rw [body_to_lime body supported]
    rfl
  | branching locals stack depth result =>
    change [AdminInstr.frame target.declaration.results.length (currentFrame target.declaration locals)
      (codeToLime (values stack ++ [.source (.br depth)]))] = _
    rw [codeToLime_append, map_values]
    rfl
  | returning locals stack =>
    change [AdminInstr.frame target.declaration.results.length (currentFrame target.declaration locals)
      (codeToLime (values stack ++ [.source .return_]))] = _
    rw [codeToLime_append, map_values]
    rfl
  | restart locals result original =>
    change [AdminInstr.frame target.declaration.results.length (currentFrame target.declaration locals)
      (codeToLime ([v1Admin.emit (.loop result original)] : List Admin))] = _
    have mapped := rest_to_lime [.loop result original] (Bool.and_eq_true_iff.mpr ⟨supported, rfl⟩)
    rw [show codeToLime ([v1Admin.emit (.loop result original)] : List Admin) =
      [limeAdmin.emit (.loop result original)] from mapped]
    rfl
  | exit locals result =>
    change [AdminInstr.frame target.declaration.results.length (currentFrame target.declaration locals)
      (codeToLime (Nested.resultCode values .trap result))] = _
    cases result with
    | trap => rfl
    | values stack =>
      change [AdminInstr.frame target.declaration.results.length (currentFrame target.declaration locals)
        (codeToLime (values stack))] = _
      rw [map_values]
      rfl
  | done result =>
    cases result with
    | trap => rfl
    | values stack => exact map_values stack

private theorem body_to_lime (q : Body) (supported : q.supportsV1 = true) :
    codeToLime (q.render v1Admin) = q.render limeAdmin := by
  cases q with
  | running stack rest =>
    change codeToLime (values stack ++ rest.map v1Admin.emit) = _
    rw [codeToLime_append, map_values, rest_to_lime rest supported]
    rfl
  | active saved target child rest =>
    obtain ⟨childOk, restOk⟩ := Bool.and_eq_true_iff.mp supported
    change codeToLime (values saved ++ child.render v1Admin target ++ rest.map v1Admin.emit) = _
    simp only [codeToLime_append, map_values, rest_to_lime rest restOk, phase_to_lime target child childOk]
    rfl
  | block saved result body rest =>
    obtain ⟨bodyOk, restOk⟩ := Bool.and_eq_true_iff.mp supported
    change codeToLime (values saved ++ .label result.toList.length [] (body.render v1Admin) :: rest.map v1Admin.emit) = _
    simp only [codeToLime_append, map_values, codeToLime_cons, AdminInstr.map, List.map_nil,
      body_to_lime body bodyOk, rest_to_lime rest restOk]
    rfl
  | indexedBlock => contradiction
  | loop saved result original body rest =>
    obtain ⟨first, restOk⟩ := Bool.and_eq_true_iff.mp supported
    obtain ⟨originalOk, bodyOk⟩ := Bool.and_eq_true_iff.mp first
    change codeToLime (values saved ++ .label 0
      [(.loop result (Op.emitList v1CodeSyntax original) : Wasm.V1.Instr)] (body.render v1Admin) ::
        rest.map v1Admin.emit) = _
    have continuation := emit_to_lime (.loop result original) originalOk
    simp only [codeToLime_append, map_values, codeToLime_cons, AdminInstr.map, List.map_cons, List.map_nil,
      body_to_lime body bodyOk, rest_to_lime rest restOk]
    rw [show Wasm.V1.Instr.toLime (.loop result (Op.emitList v1CodeSyntax original)) =
      .loop (Blocks.limeType result) (Op.emitList limeCodeSyntax original) from continuation]
    rfl
  | trapped saved rest =>
    change codeToLime (values saved ++ .trap :: rest.map v1Admin.emit) = _
    rw [codeToLime_append, map_values, codeToLime_cons, rest_to_lime rest supported]
    rfl

end

theorem config_to_lime {H : Type} (s : Store H) (caller : Frame) (target : CallTarget) (q : Phase)
    (supported : q.supportsV1 = true) :
    (v1Config s caller target q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller target q := by
  change (⟨_, _, codeToLime (q.render v1Admin target)⟩ : Wasm.Lime1.Execution.Config H) = _
  rw [phase_to_lime target q supported]
  rfl

theorem reflect_lime_step {H : Type} {s : Store H} {program : Program} (checked : program.checkV1 = true)
    (allocated : program.V1Allocated s) {caller target fn a dst}
    (root : Root program caller target fn) (ready : Admitted program fn a) (supported : a.supportsV1 = true)
    (step : Wasm.Lime1.Execution.Step CallFrame.limeNoHost (v1Config s caller target a).toLime dst) :
    ∃ mid, Step CallFrame.v1NoHost (v1Config s caller target a) mid ∧ mid.toLime = dst := by
  rw [config_to_lime s caller target a supported] at step
  obtain ⟨out, move, rfl⟩ := (Lime1.step_iff (Bool.and_eq_true_iff.mp checked).1
    (allocations_to_lime checked allocated) target.address rfl root ready).mp step
  exact ⟨_, sound checked allocated target.address rfl root ready supported move, config_to_lime s caller target out (edge_v1 checked target.address root.found move supported)⟩

theorem step_iff {H : Type} {s : Store H} {program : Program} (checked : program.checkV1 = true)
    (allocated : program.V1Allocated s) {caller target fn a dst}
    (root : Root program caller target fn) (ready : Admitted program fn a) (supported : a.supportsV1 = true) :
    Step CallFrame.v1NoHost (v1Config s caller target a) dst ↔
      ∃ out, program.Edge ((Bool.and_eq_true_iff.mp checked).1) target.address a out ∧ dst = v1Config s caller target out := by
  constructor
  · intro step
    have mapped := step.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    rw [config_to_lime s caller target a supported] at mapped
    obtain ⟨out, move, eq⟩ := (Lime1.step_iff (Bool.and_eq_true_iff.mp checked).1
      (allocations_to_lime checked allocated) target.address rfl root ready).mp mapped
    exact ⟨out, move, CallContinuation.config_toLime_injective H (eq.trans (config_to_lime s caller target out (edge_v1 checked target.address root.found move supported)).symm)⟩
  · rintro ⟨out, move, rfl⟩
    exact sound checked allocated target.address rfl root ready supported move

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.V1
