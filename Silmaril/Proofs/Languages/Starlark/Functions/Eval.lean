module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs
public import Silmaril.Languages.Starlark.Functions.Builtins.Thms
public import Silmaril.Languages.Starlark.Functions.Expressions.Thms
public import Silmaril.Languages.Starlark.Lists.Thms
public import Silmaril.Languages.Starlark.Lists.Iteration.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration
  (Flow Runs Cursor LoopTarget runs_iff_denoteSuite truth acquireIterator enterIterator denoteCursor denoteForIn
    cursor_eq_of_runs cursor_runs_denote bindTarget bindsTarget_iff_bindTarget)

private theorem branch_apply (program : Program) (available : List DeclarationId)
    (flag : Bool) (yes no : Body) (state : State) :
    (if flag then denoteBody program available yes state else denoteBody program available no state) =
      denoteBody program available (if flag then yes else no) state := by
  cases flag <;> rfl

theorem denote_eq_of_exec {program : Program} {available : List DeclarationId} {state : State}
    {body : Body} {out : Outcome Flow} (h : Exec program available state body out) :
    denoteBody program available body state = out := by
  induction h using Exec.rec
    (motive_2 := fun available target body cursor state out _ =>
      denoteCursor target (denoteBody program available body) cursor state = out)
    (motive_3 := fun available state expression out _ =>
      Lowering.denoteExprWith program available (fun plan =>
        denoteBody program (withoutDeclaration available plan.id) plan.body) expression state = out)
    (motive_4 := fun available state expressions out _ =>
      expressions.mapM (Lowering.denoteExprWith program available (fun plan =>
        denoteBody program (withoutDeclaration available plan.id) plan.body)) state = out)
  case evaluates calls ran eq =>
    exact Lowering.denoteExprWith_eq_of_evaluates eq ran
  case evaluatesMany calls ran eq =>
    exact Lowering.denoteExprsWith_eq_of_evaluatesMany eq ran
  case runs _ ran eq =>
    exact cursor_eq_of_runs eq ran
  case assignTargetExpr _ assigned evaluated =>
    simp only [denoteBody, evaluated, Outcome.resume, (bindsTarget_iff_bindTarget _ _ _ _).mp assigned]
  case assignTargetExprRhsError _ evaluated =>
    simp only [denoteBody, evaluated, Outcome.resume]
  all_goals
    (try have evaluated := (eval_iff_denote _ _ _).mp (by assumption)) <;>
    (try have total := (runs_iff_denoteSuite _ _ _).mp (by assumption)) <;>
    (try have invoked := (Builtins.invokes_iff_invoke _ _ _ _).mp (by assumption)) <;>
    simp_all [denoteBody, denoteForIn, Outcome.resume]
  case seqStop signal _ _ _ =>
    cases signal <;> simp_all <;> rfl
  case branch =>
    rw [branch_apply]
    assumption
  case branchExpr =>
    rw [branch_apply]
    assumption

private theorem exec_cursor (program : Program) (available : List DeclarationId) (target : LoopTarget)
    (body : Body) (meaning : Meaning Flow)
    (runBody : ∀ s, Exec program available s body (meaning s)) (cursor : Cursor)
    (state : State) :
    ExecCursor program available target body cursor state (denoteCursor target meaning cursor state) :=
  .runs (bodyRuns := fun s out => meaning s = out) (fun s _ eq => eq ▸ runBody s)
    (cursor_runs_denote _ meaning (fun _ => rfl) target cursor state)

theorem exec_denote (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) : Exec program available state body (denoteBody program available body state) := by
  let execute (plan : Prepared available) :=
    denoteBody program (withoutDeclaration available plan.id) plan.body
  let calls : Lowering.ClosureRuns available := fun plan next result => execute plan next = result
  have callRun (plan : Prepared available) (next : State) (result : Outcome Flow)
      (eq : calls plan next result) :
      Exec program (withoutDeclaration available plan.id) next plan.body result :=
    eq ▸ exec_denote program (withoutDeclaration available plan.id) plan.body next
  let evalExpr := Lowering.denoteExprWith program available execute
  have exprRun (expression : Lowering.Expr) (start : State) :
      ExecExpr program available start expression (evalExpr expression start) := by
    exact .evaluates callRun (Lowering.evaluatesWith_denote program available calls execute
      (fun _ _ => rfl) (Lowering.admits_all_atoms expression) start)
  cases body with
  | total code =>
    rw [denoteBody]
    exact .total ((runs_iff_denoteSuite _ _ _).mpr rfl)
  | returnExpr value =>
    rw [denoteBody]
    exact .returnExpr (exprRun value state)
  | assignExpr target value =>
    rw [denoteBody]
    exact .assignExpr (exprRun value state)
  | assignTargetExpr target rhs =>
    rw [denoteBody]
    change Exec program available state (.assignTargetExpr target rhs)
      (Outcome.resume (evalExpr rhs state) fun value next =>
        Outcome.resume (bindTarget target value next) fun () => pure .next)
    have rhsRun := exprRun rhs state
    cases evaluated : evalExpr rhs state with
    | error error next => exact .assignTargetExprRhsError (evaluated ▸ rhsRun)
    | ok value next =>
      exact .assignTargetExpr (evaluated ▸ rhsRun) ((bindsTarget_iff_bindTarget _ _ _ _).mpr rfl)
  | assignScoped target locals code =>
    rw [denoteBody]
    exact .assignScoped (exec_denote program available code (locals.foldl State.allocateSlot state))
  | setIndexExpr receiver subscript rhs =>
    rw [denoteBody]
    change Exec program available state (.setIndexExpr receiver subscript rhs)
      (Outcome.resume (evalExpr rhs state) fun value next =>
        Outcome.resume (evalExpr receiver next) fun target next =>
          Outcome.resume (evalExpr subscript next) fun index next =>
            Outcome.resume (writeIndex target index value next) fun _ => pure .next)
    have rhsRun := exprRun rhs state
    cases evaluated : evalExpr rhs state with
    | error error next => exact .setIndexExprRhsError (evaluated ▸ rhsRun)
    | ok value next =>
      simp only [Outcome.resume]
      have receiverRun := exprRun receiver next
      cases selected : evalExpr receiver next with
      | error error last => exact .setIndexExprReceiverError (evaluated ▸ rhsRun) (selected ▸ receiverRun)
      | ok target last => exact .setIndexExpr (evaluated ▸ rhsRun) (selected ▸ receiverRun) (exprRun subscript last)
  | addIndexExpr receiver subscript rhs =>
    rw [denoteBody]
    change Exec program available state (.addIndexExpr receiver subscript rhs)
      (Outcome.resume (evalExpr receiver state) fun target next =>
        Outcome.resume (evalExpr subscript next) fun index next =>
          Outcome.resume (readIndex target index next) fun previous next =>
            Outcome.resume (evalExpr rhs next) fun value next =>
              Outcome.resume (fromExcept (applyIntegerAdd previous value) next) fun sum next =>
                Outcome.resume (writeIndex target index sum next) fun _ => pure .next)
    have receiverRun := exprRun receiver state
    cases selected : evalExpr receiver state with
    | error error next => exact .addIndexExprReceiverError (selected ▸ receiverRun)
    | ok target next =>
      simp only [Outcome.resume]
      have subscriptRun := exprRun subscript next
      cases indexed : evalExpr subscript next with
      | error error last => exact .addIndexExprSubscriptError (selected ▸ receiverRun) (indexed ▸ subscriptRun)
      | ok index last =>
        dsimp only
        cases read : readIndex target index last with
        | error error stopped => exact .addIndexExprReadError (selected ▸ receiverRun) (indexed ▸ subscriptRun) read
        | ok previous ready => exact .addIndexExpr (selected ▸ receiverRun) (indexed ▸ subscriptRun) read (exprRun rhs ready)
  | evalExpr value =>
    rw [denoteBody]
    exact .evalExpr (exprRun value state)
  | insertDictEntry receiver key value =>
    rw [denoteBody]
    exact .insertDictEntry
  | seq first rest =>
    rw [denoteBody]
    have firstRun := exec_denote program available first state
    cases h : denoteBody program available first state with
    | error error next => exact .seqError (h ▸ firstRun)
    | ok flow next =>
      cases flow with
      | next => exact .seq (h ▸ firstRun) (exec_denote program available rest next)
      | breakLoop => exact .seqStop (h ▸ firstRun) (by intro equality; cases equality)
      | continueLoop => exact .seqStop (h ▸ firstRun) (by intro equality; cases equality)
      | returned result => exact .seqStop (h ▸ firstRun) (by intro equality; cases equality)
  | branch test yes no =>
    rw [denoteBody]
    have evaluated := (eval_iff_denote test state _).mpr rfl
    cases h : Outcome.resume (denote test state) truth with
    | error error next => exact .branchError evaluated h
    | ok flag next =>
      cases flag
      · exact .branch evaluated h (exec_denote program available no next)
      · exact .branch evaluated h (exec_denote program available yes next)
  | branchExpr test yes no =>
    rw [denoteBody]
    change Exec program available state (.branchExpr test yes no)
      (Outcome.resume (Outcome.resume (Lowering.denoteExprWith program available execute test state) truth)
        (fun flag next => if flag then denoteBody program available yes next
          else denoteBody program available no next))
    cases h : Outcome.resume (Lowering.denoteExprWith program available execute test state) truth with
    | error error next => exact .branchExprError (exprRun test state) h
    | ok flag next =>
      cases flag
      · exact .branchExpr (exprRun test state) h (exec_denote program available no next)
      · exact .branchExpr (exprRun test state) h (exec_denote program available yes next)
  | forIn target iterable body =>
    rw [denoteBody]
    unfold denoteForIn
    have evaluated := (eval_iff_denote iterable state _).mpr rfl
    cases h : Outcome.resume (denote iterable state) acquireIterator with
    | error error next => exact .forError evaluated h
    | ok source next =>
      obtain ⟨guard, cursor⟩ := source
      exact .forIn evaluated h (exec_cursor program available target body (denoteBody program available body)
        (exec_denote program available body) cursor (enterIterator next guard))
  | forInExpr target iterable body =>
    rw [denoteBody]
    change Exec program available state (.forInExpr target iterable body)
      (denoteForIn target (denoteBody program available body)
        (Lowering.denoteExprWith program available execute iterable state))
    unfold denoteForIn
    cases h : Outcome.resume (Lowering.denoteExprWith program available execute iterable state) acquireIterator with
    | error error next => exact .forInExprError (exprRun iterable state) h
    | ok source next =>
      obtain ⟨guard, cursor⟩ := source
      exact .forInExpr (exprRun iterable state) h (exec_cursor program available target body
        (denoteBody program available body) (exec_denote program available body) cursor (enterIterator next guard))
  | breakLoop =>
    rw [denoteBody]
    exact .breakLoop
  | continueLoop =>
    rw [denoteBody]
    exact .continueLoop
  | define target id =>
    rw [denoteBody]
    exact .define (.evaluatesMany callRun (Lowering.evaluatesManyWith_denote program available calls
      execute (fun _ _ => rfl) (defaultOperands program id)
      (fun expression _ => Lowering.admits_all_atoms expression) state))
  | call target callee arguments =>
    rw [denoteBody]
    have evaluated := (eval_iff_denote (Arguments.operands callee arguments) state _).mpr rfl
    cases h : Outcome.resume (denote (Arguments.operands callee arguments) state) (prepare program available arguments) with
    | error error next => exact .callError evaluated h
    | ok plan next =>
      cases plan with
      | closure plan =>
        exact .call evaluated h (exec_denote program (withoutDeclaration available plan.id) plan.body next)
      | builtin id actual =>
        exact .callBuiltin evaluated h ((Builtins.invokes_iff_invoke _ _ _ _).mpr rfl)
termination_by (available.length, sizeOf body)
decreasing_by
  all_goals first
    | apply Prod.Lex.right; simp_wf; omega
    | apply Prod.Lex.left
      exact List.length_filter_lt_length_iff_exists.mpr ⟨plan.id, plan.permitted, by simp⟩

end Silmaril.Proofs.Languages.Starlark.Functions
