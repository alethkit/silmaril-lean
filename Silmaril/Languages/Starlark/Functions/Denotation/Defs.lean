module

public import Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow denoteSuite truth denoteForIn bindTarget)

/-- Drop the scoped RHS bindings before applying the target binder. -/
def completeTargetAssignment (caller : State) (target : Lists.Iteration.LoopTarget) :
    Outcome Flow → Outcome Flow
  | .error error next => .error error (restoreCaller caller next)
  | .ok (.returned value) next =>
    Outcome.resume (bindTarget target value (restoreCaller caller next)) fun () => pure .next
  | .ok signal next => .ok signal (restoreCaller caller next)

/-- Structural evaluation within a frame and strict descent through the
finite set of declarations not on the call stack on invocation. -/
def denoteBody (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) : Outcome Flow :=
  let execute (plan : Prepared available) (next : State) :=
    denoteBody program (withoutDeclaration available plan.id) plan.body next
  let evalExpr := Lowering.denoteExprWith program available execute
  match body with
  | .total suite => denoteSuite suite state
  | .returnExpr value => Outcome.resume (evalExpr value state) (fun result => pure (.returned result))
  | .assignExpr target value =>
    Outcome.resume (evalExpr value state) (fun result next => .ok .next (next.write target result))
  | .assignTargetExpr target value =>
    Outcome.resume (evalExpr value state) fun result next =>
      Outcome.resume (bindTarget target result next) fun () => pure .next
  | .assignScoped target locals code =>
    completeCall state (some target)
      (denoteBody program available code (locals.foldl State.allocateSlot state))
  | .assignTargetScoped target rhs =>
    completeTargetAssignment state target (denoteBody program available rhs state)
  | .setIndexExpr receiver subscript rhs =>
    Outcome.resume (evalExpr rhs state) fun value next =>
      Outcome.resume (evalExpr receiver next) fun target next =>
        Outcome.resume (evalExpr subscript next) fun index next =>
          Outcome.resume (writeIndex target index value next) fun _ => pure .next
  | .addIndexExpr receiver subscript rhs =>
    Outcome.resume (evalExpr receiver state) fun target next =>
      Outcome.resume (evalExpr subscript next) fun index next =>
        Outcome.resume (readIndex target index next) fun previous next =>
          Outcome.resume (evalExpr rhs next) fun value next =>
            Outcome.resume (fromExcept (applyIntegerAdd previous value) next) fun sum next =>
              Outcome.resume (writeIndex target index sum next) fun _ => pure .next
  | .evalExpr value => Outcome.resume (evalExpr value state) (fun _ => pure .next)
  | .evalScoped code => completeCall state none (denoteBody program available code state)
  | .insertDictEntry receiver key value => insertDictEntry receiver key value state
  | .seq first rest =>
    Outcome.resume (denoteBody program available first state) fun
      | .next => denoteBody program available rest
      | signal => pure signal
  | .branch test yes no =>
    Outcome.resume (Outcome.resume (denote test state) truth) fun flag next =>
      if flag then denoteBody program available yes next else denoteBody program available no next
  | .branchExpr test yes no =>
    Outcome.resume (Outcome.resume (evalExpr test state) truth) fun flag next =>
      if flag then denoteBody program available yes next else denoteBody program available no next
  | .forIn target iterable body =>
    denoteForIn target (denoteBody program available body) (denote iterable state)
  | .forInExpr target iterable body =>
    denoteForIn target (denoteBody program available body) (evalExpr iterable state)
  | .breakLoop => .ok .breakLoop state
  | .continueLoop => .ok .continueLoop state
  | .define target id =>
    Outcome.resume ((defaultOperands program id).mapM evalExpr state) (define program target id)
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
    | apply Prod.Lex.right <;> simp_wf <;> omega
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
