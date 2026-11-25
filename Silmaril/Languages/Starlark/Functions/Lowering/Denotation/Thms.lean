module

public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs
public import Silmaril.Languages.Starlark.Functions.Expressions.Thms
public import Silmaril.Languages.Starlark.Functions.Thms
public import Silmaril.Languages.Starlark.Lists.Iteration.Thms

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)
open Lists.Iteration (Flow truth denoteForIn finishState iterators_denoteForIn)

/-- Every operational derivation agrees with direct denotation on the exact
result or error and final state. -/
theorem denoteExpr_eq_of_evaluates {program : Program} {available : List DeclarationId}
    {state : State} {expression : Expr} {out : Outcome Lists.Value}
    (ran : Evaluates program available state expression out) :
    denoteExpr program available expression state = out :=
  denoteExprWith_eq_of_evaluates (fun _ _ _ call => (exec_iff_denoteBody _ _ _ _ _).mp call) ran

/-- An expression with admissible atoms also has an operational derivation
for its denotational outcome. No initial heap or scratch-slot condition is needed. -/
theorem evaluates_iff_denoteExpr (program : Program) (available : List DeclarationId)
    {expression : Expr} (admitted : Admitted expression) (state : State) (out : Outcome Lists.Value) :
    Evaluates program available state expression out ↔ denoteExpr program available expression state = out :=
  ⟨denoteExpr_eq_of_evaluates,
    fun h => h ▸ evaluatesWith_denote program available (coreClosureRuns program available)
      (coreClosureMeaning program available)
      (fun _ _ => (exec_iff_denoteBody _ _ _ _ _).mpr rfl) admitted state⟩

/-- Native return delivers the direct expression result or error with its exact residual state. -/
theorem exec_returnExpr_iff_denoteExpr (program : Program) (available : List DeclarationId)
    (expression : Expr) (state : State) (out : Outcome Flow) :
    Exec program available state (.returnExpr expression) out ↔
      Outcome.resume (denoteExpr program available expression state)
        (fun value => pure (.returned value)) = out := by
  rw [exec_iff_denoteBody, denoteBody]

/-- Assignment commits the value on success and propagates the exact expression error and state. -/
theorem exec_assignExpr_iff_denoteExpr (program : Program) (available : List DeclarationId)
    (target : Binding) (expression : Expr) (state : State) (out : Outcome Flow) :
    Exec program available state (.assignExpr target expression) out ↔
      Outcome.resume (denoteExpr program available expression state)
        (fun value next => .ok .next (next.write target value)) = out := by
  rw [exec_iff_denoteBody, denoteBody]

/-- A successful test selects one body in its resulting state. Errors propagate with their state. -/
theorem exec_branchExpr_iff_denoteExpr (program : Program) (available : List DeclarationId)
    (test : Expr) (yes no : Body) (state : State) (out : Outcome Flow) :
    Exec program available state (.branchExpr test yes no) out ↔
      (Outcome.resume (Outcome.resume (denoteExpr program available test state) truth) fun flag next =>
        if flag then denoteBody program available yes next else denoteBody program available no next) = out := by
  rw [exec_iff_denoteBody, denoteBody]

/-- A native loop acquires its iterator from the exact outcome of the direct operand. -/
theorem exec_forInExpr_iff_denoteExpr (program : Program) (available : List DeclarationId)
    (target : Binding) (iterable : Expr) (body : Body) (state : State) (out : Outcome Flow) :
    Exec program available state (.forInExpr target iterable body) out ↔
      denoteForIn target (denoteBody program available body)
        (denoteExpr program available iterable state) = out := by
  rw [exec_iff_denoteBody, denoteBody]

/-- The loop restores the guard stack left by iterable evaluation on every exit. -/
theorem iterators_forInExpr (program : Program) (available : List DeclarationId)
    (target : Binding) (iterable : Expr) (body : Body) (state : State) :
    (finishState (denoteBody program available (.forInExpr target iterable body) state)).iterators =
      (finishState (denoteExpr program available iterable state)).iterators := by
  rw [denoteBody]
  exact iterators_denoteForIn target (denoteBody program available body) (denoteExpr program available iterable state)

/-- The definition evaluates defaults once in order before installing the closure.
A failed operand propagates its exact state through `Outcome.resume`. -/
theorem exec_define_iff_denoteDefaults (program : Program) (available : List DeclarationId)
    (target : Binding) (id : DeclarationId) (state : State) (out : Outcome Flow) :
    Exec program available state (.define target id) out ↔
      Outcome.resume ((defaultOperands program id).mapM (denoteExpr program available) state)
        (define program target id) = out := by
  rw [exec_iff_denoteBody, denoteBody]

end Silmaril.Languages.Starlark.Functions.Lowering
