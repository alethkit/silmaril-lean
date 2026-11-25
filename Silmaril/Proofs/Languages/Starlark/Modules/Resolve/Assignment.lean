module

public import Silmaril.Languages.Starlark.Modules.Resolve.Assignment.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Assignment

open Silmaril.Languages.Starlark (Binding Scope)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Functions.Lowering (Expr)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve
  (resolveReadValue resolveRead resolveScalar resolveExpr resolveTracked)
open Silmaril.Languages.Starlark.Functions.Comprehensions (AssignmentPattern Expression)

local notation "SourceOperand" => Silmaril.Languages.Starlark.Functions.Lowering.Resolve.SourceExpr
local notation "ResolvedOperand" => Silmaril.Languages.Starlark.Functions.Lowering.Expr

private theorem ok_bind {ε α β : Type} {first : Except ε α} {next : α → Except ε β}
    {result : β} (ran : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error => cases ran
  | ok value => exact ⟨value, rfl, ran⟩

private theorem ok_map {ε α β : Type} {first : Except ε α} {f : α → β} {result : β}
    (ran : first.map f = .ok result) : ∃ value, first = .ok value ∧ f value = result := by
  cases first with
  | error => cases ran
  | ok value => exact ⟨value, rfl, Except.ok.inj ran⟩

private theorem ok_mapError {ε δ α : Type} {first : Except ε α} {f : ε → δ} {result : α}
    (ran : first.mapError f = .ok result) : first = .ok result := by
  cases first with
  | error => cases ran
  | ok value =>
    have eq := Except.ok.inj (show Except.ok value = Except.ok result from ran)
    rw [eq]

theorem read_sound (block : LexicalBlock) (name : String) (value : ResolvedOperand) (slot : Option Binding)
    (ran : resolveReadValue block.context name = .ok (value, slot)) :
    name.toList.head? ≠ some '$' ∧ ReadResolves block name value slot.toList := by
  have legal : name.toList.head? ≠ some '$' := by
    intro banned
    simp [resolveReadValue, banned] at ran
  refine ⟨legal, ?_⟩
  by_cases owned : name ∈ block.owned
  · simp [resolveReadValue, legal, LexicalBlock.context, Silmaril.Languages.Starlark.resolveName,
      owned] at ran
    rcases ran with ⟨rfl, rfl⟩
    exact .owned owned
  by_cases enclosing : name ∈ block.enclosing
  · simp [resolveReadValue, legal, LexicalBlock.context, Silmaril.Languages.Starlark.resolveName,
      enclosing] at ran
    rcases ran with ⟨rfl, rfl⟩
    exact .enclosing owned enclosing
  by_cases global : name ∈ block.globals
  · simp [resolveReadValue, legal, LexicalBlock.context, Silmaril.Languages.Starlark.resolveName,
      owned, enclosing, global] at ran
    rcases ran with ⟨rfl, rfl⟩
    exact .global owned enclosing global
  by_cases noneName : name = "None"
  · subst name
    simp [resolveReadValue, LexicalBlock.context, Silmaril.Languages.Starlark.resolveName,
      owned, enclosing, global] at ran
    rcases ran with ⟨rfl, rfl⟩
    exact .constant owned enclosing global .none
  by_cases trueName : name = "True"
  · subst name
    simp [resolveReadValue, LexicalBlock.context, Silmaril.Languages.Starlark.resolveName,
      owned, enclosing, global] at ran
    rcases ran with ⟨rfl, rfl⟩
    exact .constant owned enclosing global .true
  by_cases falseName : name = "False"
  · subst name
    simp [resolveReadValue, LexicalBlock.context, Silmaril.Languages.Starlark.resolveName,
      owned, enclosing, global] at ran
    rcases ran with ⟨rfl, rfl⟩
    exact .constant owned enclosing global .false
  have undefined : Silmaril.Languages.Starlark.resolveName block.context.locals block.context.globals name =
      .error (.undefinedName name) := by
    unfold Silmaril.Languages.Starlark.resolveName
    have localAbsent : ¬ name ∈ block.context.locals := by simp [LexicalBlock.context, owned, enclosing]
    have globalAbsent : ¬ name ∈ block.context.globals := global
    simp [localAbsent, globalAbsent]
  simp only [resolveReadValue, legal, ite_false, undefined] at ran
  split at ran
  · rename_i builtin found
    cases ran
    exact .builtin owned enclosing global (by
      have matching := List.find?_some found
      exact beq_iff_eq.mp matching)
  · contradiction

private theorem operand_from_accumulator (block : LexicalBlock) {source : SourceOperand}
    (profile : OperandInProfile source) (initial : List Binding) (value : ResolvedOperand) (final : List Binding)
    (ran : resolveExpr block.context source initial = .ok (value, final)) :
    ∃ reads, OperandResolves block source value reads ∧ final = reads.reverse ++ initial := by
  induction profile generalizing initial value final with
  | read name =>
    rw [Silmaril.Languages.Starlark.Functions.Lowering.Resolve.resolveExpr.eq_def] at ran
    change resolveScalar block.context (.read name) initial = _ at ran
    rw [resolveScalar, resolveRead] at ran
    obtain ⟨⟨resolved, slot⟩, found, equal⟩ := ok_map ran
    have ⟨legal, resolution⟩ := read_sound block name resolved slot found
    cases equal
    exact ⟨slot.toList, .read legal resolution, by cases slot <;> rfl⟩
  | int n =>
    rw [Silmaril.Languages.Starlark.Functions.Lowering.Resolve.resolveExpr.eq_def] at ran
    change resolveScalar block.context (.int n) initial = _ at ran
    rw [resolveScalar] at ran
    change Except.ok (Expr.atom (.scalar (.int n)), initial) = _ at ran
    cases ran
    exact ⟨[], .int n, rfl⟩
  | string text =>
    rw [Silmaril.Languages.Starlark.Functions.Lowering.Resolve.resolveExpr.eq_def] at ran
    change Except.ok (Expr.atom (.string text), initial) = _ at ran
    cases ran
    exact ⟨[], .string text, rfl⟩
  | @index receiver index _ _ readReceiver readIndex =>
    rw [Silmaril.Languages.Starlark.Functions.Lowering.Resolve.resolveExpr.eq_def] at ran
    change (do
      let (recv, middle) ← resolveExpr block.context receiver initial
      let (sub, final') ← resolveExpr block.context index middle
      pure (Expr.index recv sub, final')) = _ at ran
    obtain ⟨⟨recv, middle⟩, first, ran⟩ := ok_bind ran
    obtain ⟨⟨sub, final'⟩, second, equal⟩ := ok_bind ran
    obtain ⟨receiverReads, receiverRan, middleEq⟩ := readReceiver _ _ _ first
    obtain ⟨indexReads, indexRan, finalEq⟩ := readIndex _ _ _ second
    cases equal
    exact ⟨receiverReads ++ indexReads, .index receiverRan indexRan,
      by rw [finalEq, middleEq, List.reverse_append, List.append_assoc]⟩
  | @call callee _ readCallee =>
    rw [Silmaril.Languages.Starlark.Functions.Lowering.Resolve.resolveExpr.eq_def] at ran
    change (do
      let (resolved, final') ← resolveExpr block.context callee initial
      pure (Expr.call resolved [] [] none none, final')) = _ at ran
    obtain ⟨⟨resolved, final'⟩, first, equal⟩ := ok_bind ran
    obtain ⟨reads, resolution, finalEq⟩ := readCallee _ _ _ first
    cases equal
    exact ⟨reads, .call resolution, finalEq⟩

theorem operand_sound (block : LexicalBlock) {source : SourceOperand}
    (profile : OperandInProfile source) {value : ResolvedOperand} {reads : List Binding}
    (ran : resolveTracked block.context source = .ok (value, reads)) :
    OperandResolves block source value reads := by
  unfold resolveTracked at ran
  obtain ⟨⟨resolved, final⟩, evaluated, equal⟩ := ok_map ran
  obtain ⟨ordered, related, finalEq⟩ := operand_from_accumulator block profile [] _ _ evaluated
  cases equal
  simpa [finalEq] using related

private theorem mapM_attach {ε α β : Type} (children : List α) (action : α → Except ε β) :
    (children.attach.mapM fun child => action child.val) = children.mapM action := by
  calc
    _ = (children.attach.map Subtype.val).mapM action := by simp only [List.mapM_map, Function.comp_def]
    _ = _ := by rw [List.attach_map_subtype_val]

private theorem mapM_inOrder {ε α β : Type} (children : List α) (action : α → Except ε β)
    (relation : α → β → Prop)
    (sound : ∀ child ∈ children, ∀ resolved, action child = .ok resolved → relation child resolved)
    (outputs : List β) (ran : children.mapM action = .ok outputs) :
    InOrder relation children outputs := by
  induction children generalizing outputs with
  | nil =>
    cases ran
    exact .nil
  | cons first rest ih =>
    rw [List.mapM_cons] at ran
    obtain ⟨value, head, ran⟩ := ok_bind ran
    obtain ⟨values, tail, equal⟩ := ok_bind ran
    cases equal
    exact .cons (sound first (by simp) value head)
      (ih (fun child member => sound child (List.mem_cons_of_mem _ member)) values tail)

theorem shape_sound (scope : Scope) (source : SourceOperand)
    (result : AssignmentPattern SourceOperand × List String)
    (ran : parseAssignmentPattern (fun name => ⟨scope, name⟩) source = .ok result) :
    TargetShape scope source result := by
  induction source using (measure (sizeOf : SourceOperand → Nat)).wf.induction generalizing result with
  | h source ih =>
    cases source with
      | scalar expr =>
        cases expr <;> rw [parseAssignmentPattern.eq_def] at ran <;> try cases ran
        exact .name _
      | index receiver index =>
        rw [parseAssignmentPattern.eq_def] at ran
        cases ran
        exact .subscript receiver index
      | list children | tuple children =>
        rw [parseAssignmentPattern.eq_def] at ran
        change ((children.attach.mapM (fun child => parseAssignmentPattern (fun name => ⟨scope, name⟩) child.val)) >>=
          fun shapes => Except.ok (AssignmentPattern.sequence (shapes.map Prod.fst), shapes.flatMap Prod.snd)) = _ at ran
        rw [mapM_attach] at ran
        obtain ⟨shapes, evaluated, equal⟩ := ok_bind ran
        cases equal
        have related := mapM_inOrder children _ (TargetShape scope)
          (fun child member output h =>
            ih child (by simp_wf; have := List.sizeOf_lt_of_mem member; omega) output h) shapes evaluated
        first | exact .list related | exact .tuple related
      | string _ | dict _ | slice _ _ _ _ | call _ _ _ _ _ | conditional _ _ _ | logical _ _ _ =>
        rw [parseAssignmentPattern.eq_def] at ran
        cases ran

theorem pattern_sound (block : LexicalBlock) (source : AssignmentPattern SourceOperand)
    (profile : PatternInProfile source) (result : AssignmentPattern × List Binding)
    (ran : resolveAssignmentOperands block.context source = .ok result) :
    PatternResolves block source result := by
  induction source using (measure (sizeOf : AssignmentPattern SourceOperand → Nat)).wf.induction
      generalizing result with
  | h source ih =>
    cases source with
      | name binding =>
        rw [resolveAssignmentOperands.eq_def] at ran
        cases ran
        exact .name binding
      | subscript receiver index =>
        cases profile with
        | subscript receiverProfile indexProfile =>
          rw [resolveAssignmentOperands.eq_def] at ran
          change (do
            let (recv, recvReads) ← (resolveTracked block.context receiver).mapError Error.expression
            let (sub, indexReads) ← (resolveTracked block.context index).mapError Error.expression
            pure (AssignmentPattern.subscript recv sub, recvReads ++ indexReads)) = _ at ran
          obtain ⟨⟨recv, recvReads⟩, first, ran⟩ := ok_bind ran
          obtain ⟨⟨sub, indexReads⟩, second, equal⟩ := ok_bind ran
          cases equal
          exact .subscript (operand_sound block receiverProfile (ok_mapError first))
            (operand_sound block indexProfile (ok_mapError second))
      | sequence children =>
        cases profile with
        | sequence childrenProfile =>
          rw [resolveAssignmentOperands.eq_def] at ran
          change ((children.attach.mapM (fun child => resolveAssignmentOperands block.context child.val)) >>=
            fun resolved => Except.ok (AssignmentPattern.sequence (resolved.map Prod.fst), resolved.flatMap Prod.snd)) = _ at ran
          rw [mapM_attach] at ran
          obtain ⟨resolved, evaluated, equal⟩ := ok_bind ran
          cases equal
          apply PatternResolves.sequence
          exact mapM_inOrder children _ (PatternResolves block) (fun child member output h =>
            ih child (by simp_wf; have := List.sizeOf_lt_of_mem member; omega)
              (childrenProfile child member) output h) resolved evaluated

theorem rhs_sound (block : LexicalBlock) {rhs : CompExpr} (profile : RhsInProfile rhs)
    {program next : Program} {value : Expression} {reads : List Binding}
    (ran : elaborateAssignmentRhs block.context rhs program = .ok ((value, reads), next)) :
    RhsResolves block rhs value reads ∧ next = program := by
  cases profile with
  | plain profile =>
    rw [elaborateAssignmentRhs_plain] at ran
    obtain ⟨⟨resolved, tracked⟩, found, equal⟩ := ok_map ran
    cases equal
    exact ⟨.plain (operand_sound block profile (ok_mapError found)), rfl⟩
  | @list name iterable element iterableProfile elementProfile =>
    rw [elaborateAssignmentRhs_list] at ran
    obtain ⟨⟨iterated, outer⟩, first, ran⟩ := ok_bind ran
    obtain ⟨⟨emitted, inner⟩, second, equal⟩ := ok_bind ran
    cases equal
    exact ⟨.list (operand_sound block iterableProfile (ok_mapError first))
      (operand_sound { block with owned := name :: block.owned } elementProfile (ok_mapError second)), rfl⟩

theorem elaboration_phases (block : LexicalBlock) (scope : Scope) (source : SourceOperand) (rhs : CompExpr)
    (program next : Program) (result : ResolvedPatternAssignment)
    (ran : elaboratePatternAssignment block.context scope source rhs program = .ok (result, next)) :
    (∃ shape, parseAssignmentPattern (fun name => ⟨scope, name⟩) source = .ok (shape, result.names) ∧
      resolveAssignmentOperands block.context shape = .ok (result.pattern, result.targetReads)) ∧
    elaborateAssignmentRhs block.context rhs program = .ok ((result.rhs, result.rhsReads), next) := by
  unfold elaboratePatternAssignment at ran
  obtain ⟨⟨shape, names⟩, parsed, ran⟩ := ok_bind ran
  obtain ⟨⟨⟨rhs', rhsReads⟩, next'⟩, rhsRan, ran⟩ := ok_bind ran
  obtain ⟨⟨pattern, targetReads⟩, resolved, equal⟩ := ok_bind ran
  cases equal
  exact ⟨⟨shape, parsed, resolved⟩, rhsRan⟩

theorem target_sound (block : LexicalBlock) (scope : Scope) (source : SourceOperand) (rhs : CompExpr)
    (program next : Program) (result : ResolvedPatternAssignment)
    (profile : TargetInProfile scope source)
    (ran : elaboratePatternAssignment block.context scope source rhs program = .ok (result, next)) :
    TargetResolves block scope source result.pattern result.names result.targetReads := by
  obtain ⟨⟨shape, parsed, resolved⟩, _⟩ := elaboration_phases block scope source rhs program next result ran
  have shaped := shape_sound scope source (shape, result.names) parsed
  unfold TargetResolves
  exact ⟨shape, shaped, pattern_sound block shape (profile shape result.names shaped) _ resolved⟩

theorem assignment_sound (block : LexicalBlock) (scope : Scope) (target : SourceOperand) (rhs : CompExpr)
    (program next : Program) (result : ResolvedPatternAssignment)
    (targetProfile : TargetInProfile scope target) (rhsProfile : RhsInProfile rhs)
    (ran : elaboratePatternAssignment block.context scope target rhs program = .ok (result, next)) :
    AssignmentResolves block scope target rhs result ∧ next = program := by
  have ⟨_, rhsRan⟩ := elaboration_phases block scope target rhs program next result ran
  obtain ⟨related, table⟩ := rhs_sound block rhsProfile rhsRan
  exact ⟨⟨target_sound block scope target rhs program next result targetProfile ran, related⟩, table⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Assignment
