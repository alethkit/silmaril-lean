module

public import Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions.Lowering
public import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Source.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions

open Silmaril.Languages.Starlark (Binding LogicalOp)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Comprehensions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration
open Silmaril.Proofs.Languages.Starlark.Functions.Lowering (atomScope write_slots)

private abbrev Agrees (program : Program) (available : List DeclarationId) (first second : Body) :=
  ∀ state, ScratchFree state →
    denoteBody program available first state = denoteBody program available second state

private theorem sequenceDenotation (program : Program) (available : List DeclarationId)
    (first rest : Body) (state : State) :
    denoteBody program available (.seq first rest) state =
      Outcome.resume (denoteBody program available first state) fun
      | .next => denoteBody program available rest
      | signal => pure signal := by rw [denoteBody]; rfl

private theorem seq_agrees {program : Program} {available : List DeclarationId}
    {first first' rest rest' : Body}
    (before : Exact program available first first') (after : Agrees program available rest rest') :
    Agrees program available (.seq first rest) (.seq first' rest') := by
  intro state free
  obtain ⟨equal, slots⟩ := before state free
  rw [sequenceDenotation, sequenceDenotation, ← equal]
  cases ran : denoteBody program available first state with
  | error => rfl
  | ok flow next =>
    cases flow with
    | next =>
      rw [ran] at slots
      exact after next (fun index => (congrFun slots (temporary index)).trans (free index))
    | breakLoop | continueLoop | returned => rfl

private theorem scope_exact {program : Program} {available : List DeclarationId}
    {first second : Body} (target : Binding) (inside : Agrees program available first second) :
    Exact program available (.assignScoped target [] first) (.assignScoped target [] second) := by
  intro state free
  rw [denoteBody.eq_def program available (.assignScoped _ _ first),
    denoteBody.eq_def program available (.assignScoped _ _ second)]
  let out := denoteBody program available first state
  change completeCall state (some target) out =
    completeCall state (some target) (denoteBody program available second state) ∧
    (finishState (completeCall state (some target) out)).slots = state.slots
  refine ⟨congrArg (completeCall state (some target)) (inside state free), ?_⟩
  cases out with
  | error => rfl
  | ok flow next =>
    change ((restoreCaller state next).write target (callValue flow)).slots = _
    exact write_slots _ _ _

private theorem branchDenotation (program : Program) (available : List DeclarationId)
    (test : Silmaril.Languages.Starlark.Lists.Expr) (yes no : Body) (state : State) :
    denoteBody program available (.branch test yes no) state =
      Outcome.resume (Outcome.resume (denote test state) truth) (fun flag next =>
        if flag then denoteBody program available yes next else denoteBody program available no next) := by
  rw [denoteBody] <;> rfl

private theorem branch_agrees {program : Program} {available : List DeclarationId}
    {yes no yes' no' : Body} (selected : Agrees program available yes yes')
    (skipped : Agrees program available no no') :
    Agrees program available (.branch (readSaved expressionSlot) yes no)
      (.branch (readSaved expressionSlot) yes' no') := by
  intro state free
  have visible : ¬ Scratch 0 expressionSlot := by
    rintro ⟨index, _, equal⟩
    have := congrArg Binding.scope equal
    contradiction
  have scope := (atomScope (.bound visible) state).2
  change (finishState (denote (readSaved expressionSlot) state)).slots = state.slots at scope
  rw [branchDenotation, branchDenotation]
  cases ran : denote (readSaved expressionSlot) state with
  | error => rfl
  | ok value next =>
    rw [ran] at scope
    simp only [Outcome.resume]
    have tested := truth_finishState value next
    cases checked : truth value next with
    | error => rfl
    | ok flag final =>
      rw [checked] at tested
      have kept := (congrArg State.slots tested).trans scope
      cases flag with
      | false => exact skipped final (fun index => (congrFun kept (temporary index)).trans (free index))
      | true => exact selected final (fun index => (congrFun kept (temporary index)).trans (free index))

private theorem argument_agrees {program : Program} {available : List DeclarationId} {α : Type}
    (operands : List α) (source lowered : α → Binding → Body)
    (related : ∀ item ∈ operands, ∀ target, Exact program available (source item target) (lowered item target))
    (index : Nat) (dispatch : List Silmaril.Languages.Starlark.Lists.Expr → Body) :
    Agrees program available (stageArguments index (operands.map source) dispatch)
      (stageArguments index (operands.map lowered) dispatch) := by
  induction operands generalizing index dispatch with
  | nil => exact fun _ _ => rfl
  | cons item rest ih =>
    exact seq_agrees (related item (by simp) _)
      (ih (fun item member => related item (List.mem_cons_of_mem _ member)) _ _)

theorem expression_exact (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (target : Binding) (start : Nat) :
    Exact program available (expr.body target) (expr.lower target start) := by
  unfold Expression.body Expression.lower
  rw [Expression.compile.eq_def directStages expr, Expression.compile.eq_def (loweredStages start) expr]
  cases admitted with
  | plain admitted => exact stage admitted target start
  | list outer inner locals => exact list_exact _ target start outer inner locals
  | dict outer inner locals => exact dict_exact _ target start outer inner locals
  | callPos callee arguments =>
    unfold compileCall
    apply scope_exact target
    apply seq_agrees (stage callee (argumentSlot 0) start)
    apply argument_agrees
    intro item _ destination
    have := List.sizeOf_lt_of_mem item.property
    exact expression_exact program available item.val (arguments _ item.property) destination start
  | @call callee positional keywords star starStar calleeAdmitted arguments =>
    unfold compileCall
    apply scope_exact target
    apply seq_agrees (expression_exact program available callee calleeAdmitted (argumentSlot 0) start)
    apply argument_agrees
    intro item _ destination
    have := callOperandSize callee positional keywords star starStar item.property
    exact expression_exact program available item.val (arguments _ item.property) destination start
  | branch test yes no =>
    apply scope_exact target
    apply seq_agrees (expression_exact program available _ test expressionSlot start)
    apply branch_agrees
    · exact seq_agrees (expression_exact program available _ yes expressionSlot start) (fun _ _ => rfl)
    · exact seq_agrees (expression_exact program available _ no expressionSlot start) (fun _ _ => rfl)
  | @logical op left right leftAdmitted rightAdmitted =>
    apply scope_exact target
    apply seq_agrees (expression_exact program available _ leftAdmitted expressionSlot start)
    have rightEq := seq_agrees (expression_exact program available right rightAdmitted expressionSlot start)
      (rest := returnSaved expressionSlot) (rest' := returnSaved expressionSlot) (fun _ _ => rfl)
    cases op with
    | and => exact branch_agrees rightEq (fun _ _ => rfl)
    | or => exact branch_agrees (fun _ _ => rfl) rightEq
termination_by sizeOf expr
decreasing_by all_goals first | assumption | (simp_wf; omega)

theorem return_exact (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (state : State) (free : ScratchFree state) (start : Nat) :
    denoteBody program available (expr.returnCode (loweredStages start)) state =
      denoteBody program available (expr.returnCode directStages) state :=
  (seq_agrees (expression_exact program available expr admitted expressionSlot start)
    (rest := returnSaved expressionSlot) (rest' := returnSaved expressionSlot) (fun _ _ => rfl) state free).symm

theorem logical_skips (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (op : LogicalOp) (left right : Expression) (target : Binding) (state next : State)
    (value : Value) (flag : Bool)
    (ran : denoteBody program available (left.compile stages expressionSlot) state = .ok .next next)
    (saved : denote (readSaved expressionSlot) next = .ok value next)
    (tested : truth value next = .ok flag next)
    (skip : (if op = .and then flag else !flag) = false) :
    denoteBody program available ((Expression.logical op left right).compile stages target) state =
      .ok .next ((restoreCaller state next).write target value) := by
  rw [Expression.compile.eq_def stages (.logical op left right), denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, ran]
  cases op <;> cases flag <;> simp at skip
  all_goals
    simp only [Outcome.resume]
    rw [branchDenotation, saved]
    simp only [Outcome.resume, tested, Bool.false_eq_true, ite_false, ite_true]
    rw [returnSaved, denoteBody]
    change completeCall state (some target)
      (Outcome.resume (denoteExpr program available (.atom (readSaved expressionSlot)) next)
        (fun result => pure (.returned result))) = _
    unfold denoteExpr
    rw [denoteExprWith.eq_def]
    change completeCall state (some target) (Outcome.resume (denote (readSaved expressionSlot) next)
      (fun result => pure (.returned result))) = _
    rw [saved]
    rfl

theorem conditional_selects (program : Program) (available : List DeclarationId)
    (stages : ExpressionStages) (test yes no : Expression) (target : Binding) (state next : State)
    (value : Value) (flag : Bool)
    (ran : denoteBody program available (test.compile stages expressionSlot) state = .ok .next next)
    (saved : denote (readSaved expressionSlot) next = .ok value next)
    (tested : truth value next = .ok flag next) :
    denoteBody program available ((Expression.branch test yes no).compile stages target) state =
      completeCall state (some target)
        (denoteBody program available
          (.seq ((if flag then yes else no).compile stages expressionSlot) (returnSaved expressionSlot)) next) := by
  rw [Expression.compile.eq_def stages (.branch test yes no), denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, ran]
  simp only [Outcome.resume]
  rw [branchDenotation, saved]
  simp only [Outcome.resume, tested]
  cases flag <;> rfl

theorem callee_failure (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (callee : Silmaril.Languages.Starlark.Functions.Lowering.Expr) (arguments : List Expression)
    (target : Binding) (state stopped : State) (error : Error)
    (failed : denoteBody program available (stages.plain (argumentSlot 0) callee) state = .error error stopped) :
    denoteBody program available ((Expression.callPos callee arguments).compile stages target) state =
      .error error (restoreCaller state stopped) := by
  rw [Expression.compile.eq_def stages (.callPos callee arguments)]
  dsimp only
  unfold compileCall
  rw [denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation, failed]
  rfl

theorem call_order (program : Program) (available : List DeclarationId) (target : Binding)
    (callee : Body) (shape : ArgumentShape) (operands : List (Binding → Body)) (state : State) :
    denoteBody program available (compileCall target callee shape operands) state =
      completeCall state (some target)
        (Outcome.resume (denoteBody program available callee state) fun
          | .next => denoteBody program available
              (stageArguments 1 operands fun saved =>
                .seq (.call (some expressionSlot) (readSaved (argumentSlot 0)) (fillArguments shape saved))
                  (returnSaved expressionSlot))
          | signal => pure signal) := by
  rw [compileCall, denoteBody]
  change completeCall state (some target) (denoteBody program available (.seq _ _) state) = _
  rw [sequenceDenotation] <;> rfl

theorem call_callee_failure (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (callee : Expression) (positional : List Expression) (keywords : List (String × Expression))
    (star starStar : Option Expression) (target : Binding) (state stopped : State) (error : Error)
    (failed : denoteBody program available (callee.compile stages (argumentSlot 0)) state = .error error stopped) :
    denoteBody program available ((Expression.call callee positional keywords star starStar).compile stages target) state =
      .error error (restoreCaller state stopped) := by
  rw [Expression.compile.eq_def stages (.call callee positional keywords star starStar), call_order, failed]
  rfl

theorem argument_order (program : Program) (available : List DeclarationId) (index : Nat)
    (first : Binding → Body) (rest : List (Binding → Body))
    (dispatch : List Silmaril.Languages.Starlark.Lists.Expr → Body) (state : State) :
    denoteBody program available (stageArguments index (first :: rest) dispatch) state =
      Outcome.resume (denoteBody program available (first (argumentSlot index)) state) fun
      | .next => denoteBody program available
          (stageArguments (index + 1) rest fun saved => dispatch (readSaved (argumentSlot index) :: saved))
      | signal => pure signal :=
  sequenceDenotation _ _ _ _ _

end Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions
