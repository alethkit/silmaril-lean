module

public import Silmaril.Languages.Starlark.Denotation.Defs
public import Silmaril.Languages.Starlark.Operational.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark

open Silmaril.Languages.Starlark

theorem denoteExpr_eq_of_eval {frame : Frame} {expr : ResolvedExpr} {result : Result Value}
    (h : Eval frame expr result) : denoteExpr expr frame = result := by
  induction h <;> simp_all [denoteExpr, bind, Except.bind]

theorem denoteStmt_eq_of_exec {frame : Frame} {stmt : ResolvedStmt} {result : Result Completion}
    (h : Exec frame stmt result) : denoteStmt stmt frame = result := by
  induction h <;> (try have hExpr := denoteExpr_eq_of_eval (by assumption)) <;>
    simp_all [denoteStmt, bind, Except.bind] <;> rfl

theorem eval_denoteExpr (expr : ResolvedExpr) (frame : Frame) :
    Eval frame expr (denoteExpr expr frame) := by
  induction expr with
  | int => exact .int
  | read => exact .read
  | unary op arg ih =>
    cases h : denoteExpr arg frame with
    | error error => simpa [denoteExpr, h, bind, Except.bind] using Eval.unaryError (op := op) (h ▸ ih)
    | ok value => simpa [denoteExpr, h, bind, Except.bind] using Eval.unary (op := op) (h ▸ ih)
  | binary op left right ihLeft ihRight =>
    cases hl : denoteExpr left frame with
    | error error =>
      simpa [denoteExpr, hl, bind, Except.bind] using
        Eval.binaryLeftError (op := op) (right := right) (hl ▸ ihLeft)
    | ok lhs =>
      cases hr : denoteExpr right frame with
      | error error =>
        simpa [denoteExpr, hl, hr, bind, Except.bind] using Eval.binaryRightError (op := op) (hl ▸ ihLeft) (hr ▸ ihRight)
      | ok rhs =>
        simpa [denoteExpr, hl, hr, bind, Except.bind] using Eval.binary (op := op) (hl ▸ ihLeft) (hr ▸ ihRight)
  | logical op left right ihLeft ihRight =>
    cases hl : denoteExpr left frame with
    | error error =>
      simpa [denoteExpr, hl, bind, Except.bind] using
        Eval.logicalError (op := op) (right := right) (hl ▸ ihLeft)
    | ok lhs =>
      cases h : op.runsRight lhs with
      | false =>
        simpa [denoteExpr, hl, h, bind, Except.bind] using Eval.logicalShort (right := right) (hl ▸ ihLeft) h
      | true =>
        simpa [denoteExpr, hl, h, bind, Except.bind] using Eval.logicalRight (hl ▸ ihLeft) h ihRight
  | conditional test yes no ihTest ihYes ihNo =>
    cases ht : denoteExpr test frame with
    | error error =>
      simpa [denoteExpr, ht, bind, Except.bind] using Eval.conditionalError (yes := yes) (no := no) (ht ▸ ihTest)
    | ok value =>
      cases h : value.truth with
      | false =>
        simpa [denoteExpr, ht, h, bind, Except.bind] using Eval.conditionalFalse (yes := yes) (ht ▸ ihTest) h ihNo
      | true =>
        simpa [denoteExpr, ht, h, bind, Except.bind] using Eval.conditionalTrue (no := no) (ht ▸ ihTest) h ihYes

theorem exec_denoteStmt (stmt : ResolvedStmt) (frame : Frame) :
    Exec frame stmt (denoteStmt stmt frame) := by
  induction stmt generalizing frame with
  | pass => exact .pass
  | eval expr =>
    cases h : denoteExpr expr frame with
    | error error =>
      rw [denoteStmt, h]
      exact .evalError (h ▸ eval_denoteExpr expr frame)
    | ok value =>
      rw [denoteStmt, h]
      exact .eval (h ▸ eval_denoteExpr expr frame)
  | assign name rhs =>
    cases h : denoteExpr rhs frame with
    | error error =>
      rw [denoteStmt, h]
      exact .assignError (h ▸ eval_denoteExpr rhs frame)
    | ok value =>
      rw [denoteStmt, h]
      exact .assign (h ▸ eval_denoteExpr rhs frame)
  | seq first rest ihFirst ihRest =>
    cases h : denoteStmt first frame with
    | error error =>
      rw [denoteStmt, h]
      exact .seqError (h ▸ ihFirst frame)
    | ok result =>
      obtain ⟨next, returned⟩ := result
      cases returned with
      | none =>
        rw [denoteStmt, h]
        exact .seqNext (h ▸ ihFirst frame) (ihRest next)
      | some value =>
        rw [denoteStmt, h]
        exact .seqReturn (h ▸ ihFirst frame)
  | branch test yes no ihYes ihNo =>
    cases ht : denoteExpr test frame with
    | error error =>
      rw [denoteStmt, ht]
      exact .branchError (ht ▸ eval_denoteExpr test frame)
    | ok value =>
      have hTest : Eval frame test (.ok value) := ht ▸ eval_denoteExpr test frame
      cases h : value.truth with
      | false =>
        simpa [denoteStmt, ht, h, bind, Except.bind] using Exec.branchFalse (yes := yes) hTest h (ihNo frame)
      | true =>
        simpa [denoteStmt, ht, h, bind, Except.bind] using Exec.branchTrue (no := no) hTest h (ihYes frame)
  | ret value =>
    cases value with
    | none => exact .retNone
    | some expr =>
      cases h : denoteExpr expr frame with
      | error error =>
        rw [denoteStmt, h]
        exact .retError (h ▸ eval_denoteExpr expr frame)
      | ok value =>
        rw [denoteStmt, h]
        exact .retSome (h ▸ eval_denoteExpr expr frame)

end Silmaril.Proofs.Languages.Starlark
