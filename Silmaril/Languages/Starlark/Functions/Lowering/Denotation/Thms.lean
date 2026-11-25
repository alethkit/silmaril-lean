module

public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs
public import Silmaril.Languages.Starlark.Functions.Expressions.Thms
public import Silmaril.Languages.Starlark.Functions.Thms

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)
open Lists.Iteration (Flow truth)

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

end Silmaril.Languages.Starlark.Functions.Lowering
