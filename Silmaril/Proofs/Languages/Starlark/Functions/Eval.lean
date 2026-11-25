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
  (Flow Runs runs_iff_denoteSuite truth iterationSource denoteItems denoteForIn)

private theorem branch_apply (program : Program) (available : List DeclarationId)
    (flag : Bool) (yes no : Body) (state : State) :
    (if flag then denoteBody program available yes state else denoteBody program available no state) =
      denoteBody program available (if flag then yes else no) state := by
  cases flag <;> rfl

theorem denote_eq_of_exec {program : Program} {available : List DeclarationId} {state : State}
    {body : Body} {out : Outcome Flow} (h : Exec program available state body out) :
    denoteBody program available body state = out := by
  induction h using Exec.rec
    (motive_2 := fun available target body items state out _ =>
      denoteItems target (denoteBody program available body) items state = out)
    (motive_3 := fun available state expression out _ =>
      Lowering.denoteExprWith program available (fun plan =>
        denoteBody program (withoutDeclaration available plan.id) plan.body) expression state = out)
  case evaluates calls ran eq =>
    exact Lowering.denoteExprWith_eq_of_evaluates eq ran
  all_goals
    (try have evaluated := (eval_iff_denote _ _ _).mp (by assumption)) <;>
    (try have total := (runs_iff_denoteSuite _ _ _).mp (by assumption)) <;>
    (try have invoked := (Builtins.invokes_iff_invoke _ _ _ _).mp (by assumption)) <;>
    simp_all [denoteBody, denoteForIn, denoteItems, Outcome.resume]
  case seqStop signal _ _ _ =>
    cases signal <;> simp_all <;> rfl
  case branch =>
    rw [branch_apply]
    assumption
  case branchExpr =>
    rw [branch_apply]
    assumption

private theorem exec_items (program : Program) (available : List DeclarationId) (target : Binding)
    (body : Body) (meaning : Meaning Flow)
    (runBody : ∀ s, Exec program available s body (meaning s)) (items : List Value)
    (state : State) :
    ExecItems program available target body items state (denoteItems target meaning items state) := by
  induction items generalizing state with
  | nil => exact .done
  | cons value rest ih =>
    rw [denoteItems]
    have ran := runBody (state.write target value)
    cases h : meaning (state.write target value) with
    | error error next => exact .failed (h ▸ ran)
    | ok flow next =>
      cases flow with
      | next => exact .next (h ▸ ran) (ih next)
      | continueLoop => exact .continueLoop (h ▸ ran) (ih next)
      | breakLoop => exact .breakLoop (h ▸ ran)
      | returned result => exact .returned (h ▸ ran)

theorem exec_denote (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) : Exec program available state body (denoteBody program available body state) := by
  let execute (plan : Prepared available) :=
    denoteBody program (withoutDeclaration available plan.id) plan.body
  have exprRun (expression : Lowering.Expr) :
      ExecExpr program available state expression
        (Lowering.denoteExprWith program available execute expression state) := by
    refine .evaluates (calls := fun plan next result => execute plan next = result) ?_ ?_
    · intro plan next result eq
      exact eq ▸ exec_denote program (withoutDeclaration available plan.id) plan.body next
    · exact Lowering.evaluatesWith_denote program available _ execute (fun _ _ => rfl)
        (Lowering.admits_all_atoms expression) state
  cases body with
  | total code =>
    rw [denoteBody]
    exact .total ((runs_iff_denoteSuite _ _ _).mpr rfl)
  | returnExpr value =>
    rw [denoteBody]
    exact .returnExpr (exprRun value)
  | assignExpr target value =>
    rw [denoteBody]
    exact .assignExpr (exprRun value)
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
    | error error next => exact .branchExprError (exprRun test) h
    | ok flag next =>
      cases flag
      · exact .branchExpr (exprRun test) h (exec_denote program available no next)
      · exact .branchExpr (exprRun test) h (exec_denote program available yes next)
  | forIn target iterable body =>
    rw [denoteBody]
    unfold denoteForIn
    have evaluated := (eval_iff_denote iterable state _).mpr rfl
    cases h : Outcome.resume (denote iterable state) iterationSource with
    | error error next => exact .forError evaluated h
    | ok source next =>
      obtain ⟨address, items⟩ := source
      exact .forIn evaluated h (exec_items program available target body (denoteBody program available body)
        (exec_denote program available body) items _)
  | forInExpr target iterable body =>
    rw [denoteBody]
    change Exec program available state (.forInExpr target iterable body)
      (denoteForIn target (denoteBody program available body)
        (Lowering.denoteExprWith program available execute iterable state))
    unfold denoteForIn
    cases h : Outcome.resume (Lowering.denoteExprWith program available execute iterable state) iterationSource with
    | error error next => exact .forInExprError (exprRun iterable) h
    | ok source next =>
      obtain ⟨address, items⟩ := source
      exact .forInExpr (exprRun iterable) h (exec_items program available target body
        (denoteBody program available body) (exec_denote program available body) items _)
  | breakLoop =>
    rw [denoteBody]
    exact .breakLoop
  | continueLoop =>
    rw [denoteBody]
    exact .continueLoop
  | define target id =>
    rw [denoteBody]
    exact .define ((eval_iff_denote _ _ _).mpr rfl)
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
