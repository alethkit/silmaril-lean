module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Application
public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Frame

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (LogicalOp)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (truth)

private theorem denote_call (program : Program) (available : List DeclarationId) (state : State)
    (callee : Lowering.Expr) (positional : List Lowering.Expr) (keywords : List (String × Lowering.Expr))
    (star starStar : Option Lowering.Expr) :
    denoteExpr program available (.call callee positional keywords star starStar) state =
      Outcome.resume
        ((sourceOperands callee positional keywords star starStar).mapM (denoteExpr program available) state)
        (denoteApplication program available (argumentShape positional keywords star starStar)) := by
  let args := argumentExprs positional keywords star starStar
  let meaning := denoteExpr program available
  have traverse : args.attach.mapM (fun part => meaning part.val) = args.mapM meaning := by
    change args.attach.mapM (meaning ∘ Subtype.val) = _
    rw [← List.mapM_map]
    change args.attach.unattach.mapM meaning = _
    rw [List.unattach_attach]
  rw [denoteExpr]
  change (do
    let callee ← meaning callee
    let values ← args.attach.mapM (fun (part : {expr // expr ∈ args}) => meaning part.val)
    denoteApplication program available (argumentShape positional keywords star starStar) (callee :: values)) state = _
  rw [traverse, sourceOperands]
  change _ = Outcome.resume ((callee :: args).mapM meaning state) _
  rw [List.mapM_cons]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Outcome.resume]
  cases meaning callee state with
  | error => rfl
  | ok value next =>
    dsimp only
    cases args.mapM meaning next <;> rfl

private theorem denote_branch (program : Program) (available : List DeclarationId) (state : State)
    (test yes no : Lowering.Expr) :
    denoteExpr program available (.branch test yes no) state =
      Outcome.resume (Outcome.resume (denoteExpr program available test state) truth)
        (fun flag => denoteExpr program available (if flag then yes else no)) := by
  rw [denoteExpr]
  simp only [bind, EStateM.bind, Outcome.resume]
  cases denoteExpr program available test state with
  | error => rfl
  | ok value next =>
    dsimp only
    cases truth value next with
    | error => rfl
    | ok flag state => cases flag <;> rfl

theorem denote_eq_of_evaluates {program : Program} {available : List DeclarationId} {state : State}
    {expression : Lowering.Expr} {out : Outcome Value}
    (h : Evaluates program available state expression out) :
    denoteExpr program available expression state = out := by
  induction h using Evaluates.rec
    (motive_2 := fun state expressions out _ =>
      expressions.mapM (denoteExpr program available) state = out) with
  | atom safe ran => rw [denoteExpr]; exact (eval_iff_denote _ _ _).mp ran
  | call operands applied ih =>
    rw [denote_call, ih, Outcome.resume]
    exact application_eq applied
  | callError operands ih => rw [denote_call, ih, Outcome.resume]
  | branch ran selected effective testIH branchIH =>
    rw [denote_branch, testIH, selected, Outcome.resume]
    exact branchIH
  | branchError ran failed ih => rw [denote_branch, ih, failed, Outcome.resume]
  | logical ran checked selected effective leftIH rightIH =>
    simp only [denoteExpr, bind, EStateM.bind, leftIH, checked, ite_eq_left selected]
    exact rightIH
  | shortCircuit ran checked selected ih =>
    simp [denoteExpr, bind, EStateM.bind, pure, EStateM.pure, ih, checked, selected]
  | @logicalError _ _ _ _ _ tested _ ran failed ih =>
    rw [denoteExpr]
    simp only [bind, EStateM.bind, ih]
    cases tested <;> simp_all [Outcome.resume]
  | empty => rfl
  | cons first rest firstIH restIH =>
    simp only [List.mapM_cons, bind, EStateM.bind, pure, EStateM.pure, firstIH, restIH]
  | headError ran ih => simp only [List.mapM_cons, bind, EStateM.bind, ih]
  | tailError first rest firstIH restIH =>
    simp only [List.mapM_cons, bind, EStateM.bind, firstIH, restIH]

private theorem operands_denote (program : Program) (available : List DeclarationId)
    (expressions : List Lowering.Expr)
    (each : ∀ expression ∈ expressions, ∀ state,
      Evaluates program available state expression (denoteExpr program available expression state))
    (state : State) :
    EvaluatesMany program available state expressions
      (expressions.mapM (denoteExpr program available) state) := by
  induction expressions generalizing state with
  | nil => exact .empty
  | cons expression rest ih =>
    simp only [List.mapM_cons, bind, EStateM.bind, pure, EStateM.pure]
    have first := each expression (by simp) state
    cases step : denoteExpr program available expression state with
    | error error next => exact .headError (step ▸ first)
    | ok value next =>
      dsimp only
      have restRun := ih (fun expr mem => each expr (List.mem_cons_of_mem _ mem)) next
      cases tail : rest.mapM (denoteExpr program available) next with
      | error error final => exact .tailError (step ▸ first) (tail ▸ restRun)
      | ok values final => exact .cons (step ▸ first) (tail ▸ restRun)

private theorem cons_has_value (program : Program) (available : List DeclarationId)
    (head : Lowering.Expr) (tail : List Lowering.Expr) (state final : State) :
    (head :: tail).mapM (denoteExpr program available) state ≠ .ok [] final := by
  simp only [List.mapM_cons, bind, EStateM.bind, pure, EStateM.pure]
  cases denoteExpr program available head state with
  | error => simp
  | ok value next =>
    dsimp only
    cases tail.mapM (denoteExpr program available) next <;> simp

theorem evaluates_denote (program : Program) (available : List DeclarationId)
    {expression : Lowering.Expr} (admitted : Admitted expression) (state : State) :
    Evaluates program available state expression (denoteExpr program available expression state) := by
  induction admitted generalizing state with
  | atom safe =>
    rw [denoteExpr]
    exact .atom safe ((eval_iff_denote _ _ _).mpr rfl)
  | @call callee positional keywords star starStar all ih =>
    rw [denote_call]
    let operands := sourceOperands callee positional keywords star starStar
    have ran := operands_denote program available operands ih state
    cases eval : operands.mapM (denoteExpr program available) state with
    | error error next => exact .callError (eval ▸ ran)
    | ok values next =>
      cases values with
      | nil => exact False.elim (cons_has_value program available callee _ state next eval)
      | cons callable args =>
        exact .call (eval ▸ ran) (application_denote program available _ next callable args)
  | branch _ _ _ testIH yesIH noIH =>
    rw [denote_branch]
    have ran := testIH state
    cases h : Outcome.resume (denoteExpr program available _ state) truth with
    | error error next => exact .branchError ran h
    | ok flag next =>
      cases flag
      · exact .branch ran h (noIH next)
      · exact .branch ran h (yesIH next)
  | @logical op left right _ _ leftIH rightIH =>
    rw [denoteExpr]
    simp only [bind, EStateM.bind, pure]
    have ran := leftIH state
    cases tested : denoteExpr program available left state with
    | error error next => exact .logicalError (tested ▸ ran) rfl
    | ok value next =>
      dsimp only
      cases checked : truth value next with
      | error error final => exact .logicalError (tested := .ok value next) (tested ▸ ran) checked
      | ok flag final =>
        have same := truth_frame value next
        rw [checked] at same
        change final = next at same
        subst final
        by_cases selected : (if op = .and then flag else !flag) = true
        · simpa only [ite_eq_left selected] using
            Evaluates.logical (tested ▸ ran) checked selected (rightIH next)
        · have skipped := Bool.eq_false_iff.mpr selected
          simpa [skipped, EStateM.pure] using
            Evaluates.shortCircuit (right := right) (tested ▸ ran) checked skipped

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
