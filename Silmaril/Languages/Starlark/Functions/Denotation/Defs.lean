module

public import Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow denoteSuite truth denoteForIn)

/-- Structural evaluation within a frame and strict descent through the
finite set of declarations not on the call stack on invocation. -/
def denoteBody (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) : Outcome Flow :=
  let execute (plan : Prepared available) (next : State) :=
    denoteBody program (withoutDeclaration available plan.id) plan.body next
  let evalExpr (value : Lowering.Expr) := Lowering.denoteExprWith program available execute value state
  match body with
  | .total suite => denoteSuite suite state
  | .returnExpr value => Outcome.resume (evalExpr value) (fun result => pure (.returned result))
  | .assignExpr target value =>
    Outcome.resume (evalExpr value) (fun result next => .ok .next (next.write target result))
  | .seq first rest =>
    Outcome.resume (denoteBody program available first state) fun
      | .next => denoteBody program available rest
      | signal => pure signal
  | .branch test yes no =>
    Outcome.resume (Outcome.resume (denote test state) truth) fun flag next =>
      if flag then denoteBody program available yes next else denoteBody program available no next
  | .branchExpr test yes no =>
    Outcome.resume (Outcome.resume (evalExpr test) truth) fun flag next =>
      if flag then denoteBody program available yes next else denoteBody program available no next
  | .forIn target iterable body =>
    denoteForIn target (denoteBody program available body) (denote iterable state)
  | .forInExpr target iterable body =>
    denoteForIn target (denoteBody program available body) (evalExpr iterable)
  | .breakLoop => .ok .breakLoop state
  | .continueLoop => .ok .continueLoop state
  | .define target id =>
    Outcome.resume (denote (defaultOperands program id) state) (define program target id)
  | .call target callee arguments =>
    match Outcome.resume (denote (Arguments.operands callee arguments) state) (prepare program available arguments) with
    | .error error next => .error error next
    | .ok (.closure plan) next =>
      completeCall state target (execute plan next)
    | .ok (.builtin id actual) next =>
      Outcome.resume (Builtins.invoke id actual next) (writeCallResult target)
termination_by (available.length, sizeOf body)
decreasing_by
  all_goals first
    | apply Prod.Lex.right; simp_wf; omega
    | apply Prod.Lex.left
      exact List.length_filter_lt_length_iff_exists.mpr ⟨plan.id, plan.permitted, by simp⟩

/-- Run resolved code with every declaration initially available. Use
`runChecked` to check call syntax and loop control. Install the root block's
slots before entry when they can be captured. -/
def run (program : Program) (body : Body) (state : State := {}) : Outcome Flow :=
  denoteBody program (List.range program.size) body state

/-- Check resolved signatures, explicit keywords and loop-control scope before running. -/
def runChecked (program : Program) (body : Body) (state : State := {}) :
    Except CallStaticError (Outcome Flow) := do
  validate program body
  return run program body state

end Silmaril.Languages.Starlark.Functions
