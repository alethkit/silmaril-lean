module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace

open Silmaril.Languages.Starlark (Binding resolveName)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment
open Silmaril.Languages.Starlark.Modules.Resolve.Block
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve

local notation "Expr" => Silmaril.Languages.Starlark.Functions.Lowering.Expr
local notation "Source" => SourceExpr

theorem global_operand {globals : List String} {name : String} (known : Visible globals name) :
    RootCall.Operand globals (.scalar (.read name)) (Leaf.readOperand (globalSlot name)) :=
  .global known.2 (.global (by simp) (by simp) known.1)

theorem operands_related {globals : List String} {source : Source} (allowed : Operand globals source) :
    ∃ code, RootCall.Operand globals source code := by
  induction allowed with
  | read known => exact ⟨_, global_operand known⟩
  | int n => exact ⟨_, .int n⟩
  | string text => exact ⟨_, .string text⟩
  | index _ _ left right =>
    obtain ⟨receiver, relatedReceiver⟩ := left
    obtain ⟨subscript, relatedSubscript⟩ := right
    exact ⟨.index receiver subscript, .index relatedReceiver relatedSubscript⟩

theorem actuals_related {globals : List String} (source : List Source)
    (allowed : ∀ item ∈ source, Operand globals item) :
    ∃ codes, InOrder (RootCall.Operand globals) source codes := by
  induction source with
  | nil => exact ⟨[], .nil⟩
  | cons first rest ih =>
    obtain ⟨value, related⟩ := operands_related (allowed first (by simp))
    obtain ⟨tail, remaining⟩ := ih (fun item member => allowed item (List.mem_cons_of_mem _ member))
    exact ⟨value :: tail, .cons related remaining⟩

private theorem tail_binders {globals : List String} {commands : List Command} (tail : Tail globals commands) :
    ModuleBinders commands (names commands) ∧ RootCall.Segment globals commands := by
  induction tail with
  | nil => exact ⟨.nil, .nil⟩
  | assign _ _ _ ih => exact ⟨.cons (.assign _ _) ih.1, .assign _ _ ih.2⟩

theorem schedule_binders {globals : List String} {callee : String} {chain : Chain} {commands : List Command}
    (schedule : Schedule globals callee chain commands) :
    ModuleBinders commands (names commands) ∧ RootCall.Segment globals commands := by
  induction schedule with
  | setup _ _ _ _ ih | wrapper _ _ _ ih => exact ⟨.cons (.assign _ _) ih.1, .assign _ _ ih.2⟩
  | leaf _ _ tail =>
    have rest := tail_binders tail
    exact ⟨.cons (.assign _ _) rest.1, .assign _ _ rest.2⟩

private theorem tail_legal {globals : List String} {commands : List Command}
    (tail : Tail globals commands) : ∀ name ∈ names commands, name.toList.head? ≠ some '$' := by
  induction tail with
  | nil => simp [names]
  | assign known _ _ ih =>
    intro name member
    rcases List.mem_cons.mp member with rfl | later
    · exact known.2
    · exact ih _ later

theorem schedule_legal {globals : List String} {callee : String} {chain : Chain} {commands : List Command}
    (schedule : Schedule globals callee chain commands) :
    ∀ name ∈ names commands, name.toList.head? ≠ some '$' := by
  induction schedule with
  | setup known _ _ _ ih | wrapper known _ _ ih =>
    intro name member
    rcases List.mem_cons.mp member with rfl | later
    · exact known.2
    · exact ih _ later
  | leaf known _ tail =>
    intro name member
    rcases List.mem_cons.mp member with rfl | later
    · exact known.2
    · exact tail_legal tail _ later

theorem captures_from_declared {state : Silmaril.Languages.Starlark.Lists.State}
    {free : List Silmaril.Languages.Starlark.Functions.FreeName} {captures : List Silmaril.Languages.Starlark.Lists.Capture}
    (installed : Installs state free captures)
    (legal : ∀ entry ∈ free, entry.target.name.toList.head? ≠ some '$') :
    ∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$' := by
  induction installed with
  | nil => simp
  | cons received _ ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | later
    · exact (by cases received <;> exact legal _ List.mem_cons_self)
    · exact ih (fun _ member => legal _ (List.mem_cons_of_mem _ member)) _ later

private theorem singleton_layout {parameters locals : List String} {target name : String}
    (layout : LocalBinders parameters [target] locals) :
    name ∈ parameters ++ locals ↔ name ∈ parameters ++ [target] := by
  cases layout with
  | skip present rest =>
    cases rest
    simp only [List.mem_append, List.not_mem_nil, or_false, List.mem_singleton]
    exact ⟨Or.inl, fun read => read.elim id (· ▸ present)⟩
  | keep _ rest =>
    cases rest
    rfl

private theorem lexical_name {block : LexicalBlock} {name : String}
    (visible : Visible (block.owned ++ block.enclosing ++ block.globals) name) :
    ∃ binding, binding.name = name ∧ ReadResolves block name (Leaf.readOperand binding) [binding] := by
  by_cases localName : name ∈ block.owned
  · exact ⟨fileSlot name, rfl, .owned localName⟩
  by_cases captured : name ∈ block.enclosing
  · exact ⟨fileSlot name, rfl, .enclosing localName captured⟩
  have global : name ∈ block.globals := by
    simpa [List.mem_append, localName, captured] using visible.1
  exact ⟨globalSlot name, rfl, .global localName captured global⟩

private theorem linked_name {block : LexicalBlock} {name : String}
    (visible : Visible (block.owned ++ block.enclosing ++ block.globals) name) :
    ∃ binding, binding.name = name ∧ ReadResolves block name (Leaf.readOperand binding) [binding] ∧
      resolveTracked block.context (.scalar (.read name)) = .ok (Leaf.readOperand binding, [binding]) := by
  obtain ⟨binding, named, related⟩ := lexical_name visible
  refine ⟨binding, named, related, ?_⟩
  have legal := visible.2
  unfold Leaf.readOperand at related ⊢
  rw [resolveTracked, resolveExpr.eq_def]
  cases related <;>
    simp_all [LexicalBlock.context, resolveScalar, resolveRead, resolveReadValue, resolveName,
      Except.map, List.mem_append]

private theorem visible_layout {parameters locals enclosing globals : List String} {target name : String}
    (layout : LocalBinders parameters [target] locals)
    (visible : Visible (parameters ++ target :: enclosing ++ globals) name) :
    Visible ((parameters ++ locals) ++ enclosing ++ globals) name := by
  refine ⟨?_, visible.2⟩
  have member := visible.1
  simp only [List.mem_append, List.mem_cons] at member
  simp only [List.mem_append, singleton_layout layout, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem mixedShape (target receiver index : String) :
    TargetShape .local (.tuple [.scalar (.read target), .index (.scalar (.read receiver)) (.scalar (.read index))])
      (.sequence [.name (fileSlot target), .subscript (.scalar (.read receiver)) (.scalar (.read index))], [target]) :=
  .tuple (.cons (.name target) (.cons (.subscript _ _) .nil))

private theorem target_profile (target receiver index : String) :
    TargetInProfile .local (.tuple [.scalar (.read target), .index (.scalar (.read receiver)) (.scalar (.read index))]) := by
  intro shape names related
  have exactShape := parseAssignmentPattern_complete _ _ _ (mixedShape target receiver index)
  have actual := parseAssignmentPattern_complete _ _ _ related
  rw [exactShape] at actual
  cases actual
  apply PatternInProfile.sequence
  intro child present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact .name _
  · exact .subscript (.read _) (.read _)

private theorem mixed_accepts (globals : List String) (outer : List (List String)) (program : Program)
    (name : String) (parameters locals : List String) (target rhs receiver index result : String)
    (layout : LocalBinders parameters [target] locals)
    (right : Visible (parameters ++ target :: outer.flatten ++ globals) rhs)
    (recv : Visible (parameters ++ target :: outer.flatten ++ globals) receiver)
    (offset : Visible (parameters ++ target :: outer.flatten ++ globals) index)
    (ret : Visible (parameters ++ target :: outer.flatten ++ globals) result) :
    Accepted globals program outer (.mixed name parameters
      ⟨target, .scalar (.read receiver), .scalar (.read index), .plain (.scalar (.read rhs)),
        .scalar (.read result)⟩) := by
  let block : LexicalBlock := ⟨parameters ++ locals, outer.flatten, globals⟩
  obtain ⟨rhsSlot, _, _, right⟩ := linked_name (block := block) (visible_layout layout right)
  obtain ⟨recvSlot, _, _, recv⟩ := linked_name (block := block) (visible_layout layout recv)
  obtain ⟨indexSlot, _, _, offset⟩ := linked_name (block := block) (visible_layout layout offset)
  obtain ⟨resultSlot, _, _, ret⟩ := linked_name (block := block) (visible_layout layout ret)
  let body : MixedBody :=
    ⟨target, .scalar (.read receiver), .scalar (.read index), .plain (.scalar (.read rhs)),
      .scalar (.read result)⟩
  have shape := parseAssignmentPattern_complete _ _ _ (mixedShape target receiver index)
  have declared : BodyBinders body.statement ([target] ++ []) :=
    .seq (.pattern ⟨_, mixedShape target receiver index⟩) (.ret _)
  have collected := collectFunctionLayout_eq (parentContext globals outer).reads
    (required_parameter_binders parameters) declared layout
  have staged : resolveAssignmentOperands block.context
      (.sequence [.name (fileSlot target), .subscript (.scalar (.read receiver)) (.scalar (.read index))]) =
      .ok (.sequence [.name (fileSlot target), .subscript (Leaf.readOperand recvSlot) (Leaf.readOperand indexSlot)],
        [recvSlot, indexSlot]) := by
    have nameRead : resolveAssignmentOperands block.context (.name (fileSlot target)) =
        .ok (.name (fileSlot target), []) := by rw [resolveAssignmentOperands]; rfl
    have subRead : resolveAssignmentOperands block.context
        (.subscript (.scalar (.read receiver)) (.scalar (.read index))) =
        .ok (.subscript (Leaf.readOperand recvSlot) (Leaf.readOperand indexSlot), [recvSlot, indexSlot]) := by
      rw [resolveAssignmentOperands]
      simp [recv, offset, Except.mapError, bind, Except.bind, pure, Except.pure]
    rw [resolveAssignmentOperands]
    simp [List.mapM_cons, nameRead, subRead, bind, Except.bind, pure, Except.pure]
  refine .mixed (body := body) (next := program) (locals := locals)
    (assignment := ⟨.sequence [.name (fileSlot target),
        .subscript (Leaf.readOperand recvSlot) (Leaf.readOperand indexSlot)],
      .plain (Leaf.readOperand rhsSlot), [target], [rhsSlot], [recvSlot, indexSlot]⟩) layout
    (target_profile target receiver index) (.plain (.read _)) (.read _) ?_ ret
  rw [collected]
  change elaboratePatternAssignment block.context .local body.target body.rhs program = _
  unfold elaboratePatternAssignment
  rw [show ((fun name => (⟨.local, name⟩ : Binding))) = fileSlot from rfl]
  change parseAssignmentPattern fileSlot _ = _ at shape
  simp [body, MixedBody.target, shape, elaborateAssignmentRhs_plain, right, staged, Except.mapError,
    Except.map, bind, Except.bind, pure, Except.pure]

theorem definitions_accept {globals : List String} {chain : Chain} {enclosing : List String}
    (profile : Definitions globals enclosing chain) (program : Program) (outer : List (List String))
    (same : ∀ name, name ∈ outer.flatten ↔ name ∈ enclosing) :
    Accepted globals program outer chain := by
  induction profile generalizing outer with
  | @mixed enclosing params name target rhs receiver index result _ _ right recv offset ret =>
    obtain ⟨locals, layout⟩ := localBinders_exists params [target]
    have transport {name : String} (visible : Visible (params ++ target :: enclosing ++ globals) name) :
        Visible (params ++ target :: outer.flatten ++ globals) name := by
      simpa [Visible, List.mem_append, same] using visible
    exact mixed_accepts globals outer program name params locals target rhs receiver index result layout
      (transport right) (transport recv) (transport offset) (transport ret)
  | @wrapper enclosing params name child _ legal _ ih =>
    obtain ⟨locals, layout⟩ := localBinders_exists params [child.name]
    apply Accepted.wrapper layout legal
    apply ih
    intro name
    simp only [List.flatten_cons, List.mem_append, same, List.mem_cons]
    have layoutName : name ∈ params ∨ name ∈ locals ↔ name ∈ params ∨ name = child.name := by
      simpa [List.mem_append] using (singleton_layout (name := name) layout)
    rw [layoutName]
    tauto

theorem leaf_plan {globals : List String} {outer : List (List String)} {enclosing : List String}
    {name : String} {parameters : List String} {body : MixedBody} {frame : Frame} {rest : List Frame}
    (profile : Definitions globals enclosing (.mixed name parameters body))
    (scopes : ∀ name, name ∈ outer.flatten ↔ name ∈ enclosing)
    (emits : Emits globals outer (.mixed name parameters body) (frame :: rest)) :
    ∃ plan, Leaf.Resolves ⟨frame.owned, outer.flatten, globals⟩ body plan ∧ plan.Legal ∧
      (∀ name ∈ frame.owned, name.toList.head? ≠ some '$') := by
  cases profile with
  | @mixed _ _ _ target rhs receiver index result paramsLegal targetLegal right recv offset ret =>
    cases emits with
    | @mixed _ _ _ locals _ _ _ _ layout =>
      have admitted {name : String} (visible : Visible (parameters ++ target :: enclosing ++ globals) name) :
          Visible ((parameters ++ locals) ++ outer.flatten ++ globals) name := by
        apply visible_layout layout
        simpa [Visible, List.mem_append, scopes] using visible
      obtain ⟨rhsSlot, rhsName, rightRead⟩ := lexical_name (block := ⟨parameters ++ locals, outer.flatten, globals⟩) (admitted right)
      obtain ⟨recvSlot, recvName, recvRead⟩ := lexical_name (block := ⟨parameters ++ locals, outer.flatten, globals⟩) (admitted recv)
      obtain ⟨indexSlot, indexName, indexRead⟩ := lexical_name (block := ⟨parameters ++ locals, outer.flatten, globals⟩) (admitted offset)
      obtain ⟨resultSlot, resultName, retRead⟩ := lexical_name (block := ⟨parameters ++ locals, outer.flatten, globals⟩) (admitted ret)
      refine ⟨_, .reads _ _ _ _ _ rhsSlot recvSlot indexSlot resultSlot rightRead recvRead indexRead retRead, ?_, ?_⟩
      · intro binding member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl
        · exact targetLegal
        · simpa [rhsName] using right.2
        · simpa [recvName] using recv.2
        · simpa [indexName] using offset.2
        · simpa [resultName] using ret.2
      · intro identifier member
        have actual := (singleton_layout layout).mp member
        rcases List.mem_append.mp actual with parameter | target
        · exact paramsLegal _ parameter
        · cases List.mem_singleton.mp target
          exact targetLegal

theorem singleton_legal {parameters locals : List String} {binder : String}
    (layout : LocalBinders parameters [binder] locals)
    (parametersLegal : ∀ name ∈ parameters, name.toList.head? ≠ some '$')
    (binderLegal : binder.toList.head? ≠ some '$') :
    ∀ name ∈ parameters ++ locals, name.toList.head? ≠ some '$' := by
  intro name member
  have actual := (singleton_layout layout).mp member
  rcases List.mem_append.mp actual with parameter | bound
  · exact parametersLegal _ parameter
  · cases List.mem_singleton.mp bound
    exact binderLegal

theorem capture_names_from_slots {state : Silmaril.Languages.Starlark.Lists.State}
    {free : List Silmaril.Languages.Starlark.Functions.FreeName}
    {captures : List Silmaril.Languages.Starlark.Lists.Capture} (installed : Installs state free captures)
    (clean : Leaf.noPrivateSlots state) :
    ∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$' := by
  induction installed with
  | nil => simp
  | cons here _ ih =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | later
    · intro secret
      cases here with
      | enclosing slot | forwardedLocal slot | ownedGlobal slot | capturedGlobal slot =>
        rw [clean _ secret] at slot
        contradiction
    · exact ih _ later

theorem child_scopes {parameters locals enclosing : List String} {child : Chain} {outer : List (List String)}
    (layout : LocalBinders parameters [child.name] locals)
    (same : ∀ name, name ∈ outer.flatten ↔ name ∈ enclosing) :
    ∀ name, name ∈ ((parameters ++ locals) :: outer).flatten ↔ name ∈ (parameters ++ child.name :: enclosing) := by
  intro name
  simp only [List.flatten_cons, List.mem_append, same, List.mem_cons]
  have layoutName : name ∈ parameters ∨ name ∈ locals ↔ name ∈ parameters ∨ name = child.name := by
    simpa [List.mem_append] using (singleton_layout (name := name) layout)
  rw [layoutName]
  tauto

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace
