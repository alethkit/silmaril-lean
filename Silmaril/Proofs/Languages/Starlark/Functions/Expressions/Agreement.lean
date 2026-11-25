module

public import Silmaril.Proofs.Languages.Starlark.Functions.Expressions.Application
public import Silmaril.Languages.Starlark.Lists.Thms
public import Silmaril.Languages.Starlark.Lists.Iteration.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Expressions

open Silmaril.Languages.Starlark (LogicalOp)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (truth truth_finishState)

private theorem denote_list (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (state : State) (elements : List Lowering.Expr) :
    denoteExprWith program available bodyMeaning (.list elements) state =
      Outcome.resume (elements.mapM (denoteExprWith program available bodyMeaning) state) allocate := by
  let meaning := denoteExprWith program available bodyMeaning
  have traverse : elements.attach.mapM (meaning ∘ Subtype.val) = elements.mapM meaning := by
    rw [← List.mapM_map]
    change elements.attach.unattach.mapM meaning = _
    rw [List.unattach_attach]
  rw [denoteExprWith]
  change Outcome.resume (elements.attach.mapM (meaning ∘ Subtype.val) state) allocate = _
  rw [traverse]

private theorem denote_tuple (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (state : State) (elements : List Lowering.Expr) :
    denoteExprWith program available bodyMeaning (.tuple elements) state =
      Outcome.resume (elements.mapM (denoteExprWith program available bodyMeaning) state) allocateTuple := by
  let meaning := denoteExprWith program available bodyMeaning
  have traverse : elements.attach.mapM (meaning ∘ Subtype.val) = elements.mapM meaning := by
    rw [← List.mapM_map]
    change elements.attach.unattach.mapM meaning = _
    rw [List.unattach_attach]
  rw [denoteExprWith]
  change Outcome.resume (elements.attach.mapM (meaning ∘ Subtype.val) state) allocateTuple = _
  rw [traverse]

private theorem denote_index (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (state : State) (receiver subscript : Lowering.Expr) :
    denoteExprWith program available bodyMeaning (.index receiver subscript) state =
      Outcome.resume (denoteExprWith program available bodyMeaning receiver state) (fun value next =>
        Outcome.resume (denoteExprWith program available bodyMeaning subscript next) (readIndex value)) := by
  rw [denoteExprWith]

private theorem denote_slice (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (state : State) (receiver start stop stride : Lowering.Expr) :
    denoteExprWith program available bodyMeaning (.slice receiver start stop stride) state =
      Outcome.resume ([receiver, start, stop, stride].mapM (denoteExprWith program available bodyMeaning) state)
        readSliceOperands := by
  rw [denoteExprWith]
  let operands := [receiver, start, stop, stride]
  let meaning := denoteExprWith program available bodyMeaning
  change Outcome.resume (operands.attach.mapM (meaning ∘ Subtype.val) state) readSliceOperands = _
  rw [← List.mapM_map]
  change Outcome.resume (operands.attach.unattach.mapM meaning state) readSliceOperands = _
  rw [List.unattach_attach]

private theorem denote_dict (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (state : State) (entries : List (Lowering.Expr × Lowering.Expr)) :
    let meaning := denoteExprWith program available bodyMeaning
    denoteExprWith program available bodyMeaning (.dict entries) state =
      Outcome.resume (allocateDict [] state) fun receiver next =>
        Outcome.resume (denoteEntries receiver (entries.map fun (key, value) => (meaning key, meaning value)) next)
          fun _ => pure receiver := by
  dsimp only
  let meaning := denoteExprWith program available bodyMeaning
  let actions := fun (pair : Lowering.Expr × Lowering.Expr) => (meaning pair.1, meaning pair.2)
  have traverse : entries.attach.map (actions ∘ Subtype.val) = entries.map actions := by
    rw [← List.map_map]
    change entries.attach.unattach.map actions = _
    rw [List.unattach_attach]
  rw [denoteExprWith]
  change Outcome.resume (allocateDict [] state) (fun receiver next =>
    Outcome.resume (denoteEntries receiver (entries.attach.map (actions ∘ Subtype.val)) next)
      fun _ => pure receiver) = _
  rw [traverse]

private theorem denote_call (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (state : State)
    (callee : Lowering.Expr) (positional : List Lowering.Expr) (keywords : List (String × Lowering.Expr))
    (star starStar : Option Lowering.Expr) :
    denoteExprWith program available bodyMeaning (.call callee positional keywords star starStar) state =
      Outcome.resume
        ((sourceOperands callee positional keywords star starStar).mapM (denoteExprWith program available bodyMeaning) state)
        (denoteApplicationWith program available bodyMeaning (argumentShape positional keywords star starStar)) := by
  let args := argumentExprs positional keywords star starStar
  let meaning := denoteExprWith program available bodyMeaning
  have traverse : args.attach.mapM (fun part => meaning part.val) = args.mapM meaning := by
    change args.attach.mapM (meaning ∘ Subtype.val) = _
    rw [← List.mapM_map]
    change args.attach.unattach.mapM meaning = _
    rw [List.unattach_attach]
  rw [denoteExprWith]
  change (do
    let callee ← meaning callee
    let values ← args.attach.mapM (fun (part : {expr // expr ∈ args}) => meaning part.val)
    denoteApplicationWith program available bodyMeaning (argumentShape positional keywords star starStar) (callee :: values)) state = _
  rw [traverse, sourceOperands]
  change _ = Outcome.resume ((callee :: args).mapM meaning state) _
  rw [List.mapM_cons]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Outcome.resume]
  cases meaning callee state with
  | error => rfl
  | ok value next =>
    dsimp only
    cases args.mapM meaning next <;> rfl

private theorem denote_branch (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (state : State)
    (test yes no : Lowering.Expr) :
    denoteExprWith program available bodyMeaning (.branch test yes no) state =
      Outcome.resume (Outcome.resume (denoteExprWith program available bodyMeaning test state) truth)
        (fun flag => denoteExprWith program available bodyMeaning (if flag then yes else no)) := by
  rw [denoteExprWith]
  simp only [bind, EStateM.bind, Outcome.resume]
  cases denoteExprWith program available bodyMeaning test state with
  | error => rfl
  | ok value next =>
    dsimp only
    cases truth value next with
    | error => rfl
    | ok flag state => cases flag <;> rfl

theorem denote_eq_of_evaluates {program : Program} {available : List DeclarationId} {state : State}
    {expression : Lowering.Expr} {out : Outcome Value}
    {calls : ClosureRuns available} {bodyMeaning : ClosureMeaning available}
    {atomAllowed : Silmaril.Languages.Starlark.Lists.Expr → Prop}
    (closureEq : ∀ plan state out, calls plan state out → bodyMeaning plan state = out)
    (h : EvaluatesWith program available calls atomAllowed state expression out) :
    denoteExprWith program available bodyMeaning expression state = out := by
  induction h using EvaluatesWith.rec
    (motive_2 := fun state expressions out _ =>
      expressions.mapM (denoteExprWith program available bodyMeaning) state = out)
    (motive_3 := fun receiver state entries out _ =>
      denoteEntries receiver (entries.map fun pair =>
        (denoteExprWith program available bodyMeaning pair.1,
          denoteExprWith program available bodyMeaning pair.2)) state = out) with
  | atom safe ran => rw [denoteExprWith]; exact (eval_iff_denote _ _ _).mp ran
  | list ran ih => rw [denote_list, ih]
  | tuple ran ih => rw [denote_tuple, ih]
  | dict allocated ran ih => simp only [denote_dict, allocated, Outcome.resume, ih]
  | index receiver subscript receiverIH subscriptIH =>
    simp only [denote_index, receiverIH, Outcome.resume, subscriptIH]
  | indexReceiverError ran ih => simp only [denote_index, ih, Outcome.resume]
  | slice ran ih => rw [denote_slice, ih]
  | call operands applied ih =>
    rw [denote_call, ih, Outcome.resume]
    exact application_eq closureEq applied
  | callError operands ih => rw [denote_call, ih, Outcome.resume]
  | branch ran selected effective testIH branchIH =>
    rw [denote_branch, testIH, selected, Outcome.resume]
    exact branchIH
  | branchError ran failed ih => rw [denote_branch, ih, failed, Outcome.resume]
  | logical ran checked selected effective leftIH rightIH =>
    simp only [denoteExprWith, bind, EStateM.bind, leftIH, checked, ite_eq_left selected]
    exact rightIH
  | shortCircuit ran checked selected ih =>
    simp [denoteExprWith, bind, EStateM.bind, pure, EStateM.pure, ih, checked, selected]
  | @logicalError _ _ _ _ _ tested _ ran failed ih =>
    rw [denoteExprWith]
    simp only [bind, EStateM.bind, ih]
    cases tested <;> simp_all [Outcome.resume]
  | empty => rfl
  | cons first rest firstIH restIH =>
    simp only [List.mapM_cons, bind, EStateM.bind, pure, EStateM.pure, firstIH, restIH]
  | headError ran ih => simp only [List.mapM_cons, bind, EStateM.bind, ih]
  | tailError first rest firstIH restIH =>
    simp only [List.mapM_cons, bind, EStateM.bind, firstIH, restIH]
  | noEntries => rfl
  | keyError ran ih => simp only [List.map_cons, denoteEntries, ih, Outcome.resume]
  | valueError key value keyIH valueIH =>
    simp only [List.map_cons, denoteEntries, keyIH, valueIH, Outcome.resume]
  | insertionError key value inserted keyIH valueIH =>
    simp only [List.map_cons, denoteEntries, keyIH, valueIH, inserted, Outcome.resume]
  | entry key value inserted rest keyIH valueIH restIH =>
    simp only [List.map_cons, denoteEntries, keyIH, valueIH, inserted, Outcome.resume, restIH]

theorem denote_eq_of_evaluatesMany {program : Program} {available : List DeclarationId}
    {calls : ClosureRuns available} {bodyMeaning : ClosureMeaning available}
    {atomAllowed : Silmaril.Languages.Starlark.Lists.Expr → Prop}
    (closureEq : ∀ plan state out, calls plan state out → bodyMeaning plan state = out)
    {state : State} {expressions : List Lowering.Expr} {out : Outcome (List Value)}
    (ran : EvaluatesManyWith program available calls atomAllowed state expressions out) :
    expressions.mapM (denoteExprWith program available bodyMeaning) state = out := by
  induction expressions generalizing state out with
  | nil => cases ran; rfl
  | cons expression rest ih =>
    cases ran with
    | cons first tail =>
      simp only [List.mapM_cons, bind, EStateM.bind, pure, EStateM.pure,
        denote_eq_of_evaluates closureEq first, ih tail]
    | headError first =>
      simp only [List.mapM_cons, bind, EStateM.bind, denote_eq_of_evaluates closureEq first]
    | tailError first tail =>
      simp only [List.mapM_cons, bind, EStateM.bind, denote_eq_of_evaluates closureEq first, ih tail]

private theorem operands_denote (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    {atomAllowed : Silmaril.Languages.Starlark.Lists.Expr → Prop} (expressions : List Lowering.Expr)
    (each : ∀ expression ∈ expressions, ∀ state,
      EvaluatesWith program available calls atomAllowed state expression (denoteExprWith program available bodyMeaning expression state))
    (state : State) :
    EvaluatesManyWith program available calls atomAllowed state expressions
      (expressions.mapM (denoteExprWith program available bodyMeaning) state) := by
  induction expressions generalizing state with
  | nil => exact .empty
  | cons expression rest ih =>
    simp only [List.mapM_cons, bind, EStateM.bind, pure, EStateM.pure]
    have first := each expression (by simp) state
    cases step : denoteExprWith program available bodyMeaning expression state with
    | error error next => exact .headError (step ▸ first)
    | ok value next =>
      dsimp only
      have restRun := ih (fun expr mem => each expr (List.mem_cons_of_mem _ mem)) next
      cases tail : rest.mapM (denoteExprWith program available bodyMeaning) next with
      | error error final => exact .tailError (step ▸ first) (tail ▸ restRun)
      | ok values final => exact .cons (step ▸ first) (tail ▸ restRun)

private theorem cons_has_value (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (head : Lowering.Expr) (tail : List Lowering.Expr) (state final : State) :
    (head :: tail).mapM (denoteExprWith program available bodyMeaning) state ≠ .ok [] final := by
  simp only [List.mapM_cons, bind, EStateM.bind, pure, EStateM.pure]
  cases denoteExprWith program available bodyMeaning head state with
  | error => simp
  | ok value next =>
    dsimp only
    cases tail.mapM (denoteExprWith program available bodyMeaning) next <;> simp

private theorem entries_denote (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    {atomAllowed : Silmaril.Languages.Starlark.Lists.Expr → Prop}
    (receiver : Value) (entries : List (Lowering.Expr × Lowering.Expr)) (state : State)
    (keys : ∀ entry ∈ entries, ∀ state,
      EvaluatesWith program available calls atomAllowed state entry.1 (denoteExprWith program available bodyMeaning entry.1 state))
    (values : ∀ entry ∈ entries, ∀ state,
      EvaluatesWith program available calls atomAllowed state entry.2 (denoteExprWith program available bodyMeaning entry.2 state)) :
    EvaluatesEntriesWith program available calls atomAllowed receiver state entries
      (denoteEntries receiver (entries.map fun pair =>
        (denoteExprWith program available bodyMeaning pair.1,
          denoteExprWith program available bodyMeaning pair.2)) state) := by
  induction entries generalizing state with
  | nil => exact .noEntries
  | cons pair rest ih =>
    obtain ⟨key, value⟩ := pair
    simp only [List.map_cons, denoteEntries]
    have keyRun := keys (key, value) (by simp) state
    dsimp only at keyRun
    cases keyEq : denoteExprWith program available bodyMeaning key state with
    | error error next => exact .keyError (keyEq ▸ keyRun)
    | ok k next =>
      simp only [Outcome.resume]
      have valueRun := values (key, value) (by simp) next
      dsimp only at valueRun
      cases valueEq : denoteExprWith program available bodyMeaning value next with
      | error error final => exact .valueError (keyEq ▸ keyRun) (valueEq ▸ valueRun)
      | ok v final =>
        dsimp only
        cases inserted : insertDisplayEntry receiver k v final with
        | error error stopped => exact .insertionError (keyEq ▸ keyRun) (valueEq ▸ valueRun) inserted
        | ok result stopped =>
          cases result
          exact .entry (keyEq ▸ keyRun) (valueEq ▸ valueRun) inserted
            (ih stopped (fun pair mem => keys pair (List.mem_cons_of_mem _ mem))
              (fun pair mem => values pair (List.mem_cons_of_mem _ mem)))

theorem evaluates_denote (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    (closureComplete : ∀ plan state, calls plan state (bodyMeaning plan state))
    {atomAllowed : Silmaril.Languages.Starlark.Lists.Expr → Prop} {expression : Lowering.Expr}
    (admitted : AdmittedWith atomAllowed expression) (state : State) :
    EvaluatesWith program available calls atomAllowed state expression (denoteExprWith program available bodyMeaning expression state) := by
  induction admitted generalizing state with
  | atom safe =>
    rw [denoteExprWith]
    exact .atom safe ((eval_iff_denote _ _ _).mpr rfl)
  | @list elements all ih =>
    rw [denote_list]
    exact .list (operands_denote program available calls bodyMeaning elements ih state)
  | @tuple elements all ih =>
    rw [denote_tuple]
    exact .tuple (operands_denote program available calls bodyMeaning elements ih state)
  | @dict entries _ _ keyIH valueIH =>
    rw [denote_dict]
    let receiver := Value.dict state.heap.size
    let next := { state with heap := state.heap.push ⟨.dict [], false⟩ }
    exact .dict (receiver := receiver) (t := next) rfl
      (entries_denote program available calls bodyMeaning receiver entries next keyIH valueIH)
  | @index receiver subscript _ _ receiverIH subscriptIH =>
    rw [denote_index]
    have ran := receiverIH state
    cases tested : denoteExprWith program available bodyMeaning receiver state with
    | error error next => exact .indexReceiverError (tested ▸ ran)
    | ok value next => exact .index (tested ▸ ran) (subscriptIH next)
  | @slice receiver start stop stride _ ih =>
    rw [denote_slice]
    exact .slice (operands_denote program available calls bodyMeaning [receiver, start, stop, stride] ih state)
  | @call callee positional keywords star starStar all ih =>
    rw [denote_call]
    let operands := sourceOperands callee positional keywords star starStar
    have ran := operands_denote program available calls bodyMeaning operands ih state
    cases eval : operands.mapM (denoteExprWith program available bodyMeaning) state with
    | error error next => exact .callError (eval ▸ ran)
    | ok values next =>
      cases values with
      | nil => exact False.elim (cons_has_value program available bodyMeaning callee _ state next eval)
      | cons callable args =>
        exact .call (eval ▸ ran)
          (application_denote program available _ calls bodyMeaning closureComplete next callable args)
  | branch _ _ _ testIH yesIH noIH =>
    rw [denote_branch]
    have ran := testIH state
    cases h : Outcome.resume (denoteExprWith program available bodyMeaning _ state) truth with
    | error error next => exact .branchError ran h
    | ok flag next =>
      cases flag
      · exact .branch ran h (noIH next)
      · exact .branch ran h (yesIH next)
  | @logical op left right _ _ leftIH rightIH =>
    rw [denoteExprWith]
    simp only [bind, EStateM.bind, pure]
    have ran := leftIH state
    cases tested : denoteExprWith program available bodyMeaning left state with
    | error error next => exact .logicalError (tested ▸ ran) rfl
    | ok value next =>
      dsimp only
      cases checked : truth value next with
      | error error final => exact .logicalError (tested := .ok value next) (tested ▸ ran) checked
      | ok flag final =>
        have same := truth_finishState value next
        rw [checked] at same
        change final = next at same
        subst final
        by_cases selected : (if op = .and then flag else !flag) = true
        · simpa only [ite_eq_left selected] using
            EvaluatesWith.logical (tested ▸ ran) checked selected (rightIH next)
        · have skipped := Bool.eq_false_iff.mpr selected
          simpa [skipped, EStateM.pure] using
            EvaluatesWith.shortCircuit (right := right) (tested ▸ ran) checked skipped

theorem evaluatesMany_denote (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    (closureComplete : ∀ plan state, calls plan state (bodyMeaning plan state))
    {atomAllowed : Silmaril.Languages.Starlark.Lists.Expr → Prop}
    (expressions : List Lowering.Expr)
    (admitted : ∀ expression ∈ expressions, AdmittedWith atomAllowed expression) (state : State) :
    EvaluatesManyWith program available calls atomAllowed state expressions
      (expressions.mapM (denoteExprWith program available bodyMeaning) state) :=
  operands_denote program available calls bodyMeaning expressions
    (fun expression member => evaluates_denote program available calls bodyMeaning closureComplete
      (admitted expression member)) state

theorem denote_atom_operands (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (operands : List Silmaril.Languages.Starlark.Lists.Expr)
    (state : State) :
    (operands.map Lowering.Expr.atom).mapM (denoteExprWith program available bodyMeaning) state =
      denote (operandList operands) state := by
  induction operands generalizing state with
  | nil => rfl
  | cons expression rest ih =>
    simp only [List.map_cons, List.mapM_cons, denoteExprWith, operandList, List.foldr_cons,
      denote, bind, EStateM.bind, pure, EStateM.pure]
    cases denote expression state with
    | error => rfl
    | ok value next =>
      dsimp only
      rw [ih next]
      rfl

theorem admits_all_atoms (expression : Lowering.Expr) : AdmittedWith (fun _ => True) expression := by
  cases expression with
  | atom => exact .atom trivial
  | list elements =>
    refine .list ?_
    intro element member
    have := List.sizeOf_lt_of_mem member
    exact admits_all_atoms element
  | tuple elements =>
    refine .tuple ?_
    intro element member
    have := List.sizeOf_lt_of_mem member
    exact admits_all_atoms element
  | dict entries =>
    constructor
    · rintro ⟨key, value⟩ member
      have := (entrySize member).1
      exact admits_all_atoms key
    · rintro ⟨key, value⟩ member
      have := (entrySize member).2
      exact admits_all_atoms value
  | index receiver subscript => exact .index (admits_all_atoms receiver) (admits_all_atoms subscript)
  | slice receiver start stop stride =>
    refine .slice fun operand member => ?_
    have := sliceOperandSize member
    exact admits_all_atoms operand
  | logical op left right => exact .logical (admits_all_atoms left) (admits_all_atoms right)
  | branch test yes no =>
    exact .branch (admits_all_atoms test) (admits_all_atoms yes) (admits_all_atoms no)
  | call callee positional keywords star starStar =>
    refine .call ?_
    intro operand member
    change operand ∈ callee :: argumentExprs positional keywords star starStar at member
    rcases List.mem_cons.mp member with found | argument
    · subst operand
      exact admits_all_atoms callee
    · have := argumentSize callee positional keywords star starStar argument
      exact admits_all_atoms operand
termination_by sizeOf expression
decreasing_by all_goals first | assumption | (simp_wf; omega)

end Silmaril.Proofs.Languages.Starlark.Functions.Expressions
