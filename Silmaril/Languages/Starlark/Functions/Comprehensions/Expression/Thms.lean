module

public import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Source.Defs
public import Silmaril.Languages.Starlark.Functions.Comprehensions.Thms
import Silmaril.Proofs.Languages.Starlark.Functions.Comprehensions.Expression

public section

namespace Silmaril.Languages.Starlark.Functions.Comprehensions

open Lists (State Outcome denote)
open Lists.Iteration (Flow truth)

/-- The independently defined body rules determine the exact outcome of a
resolved expression assignment. -/
theorem Expression.exec_iff_denote (program : Program) (available : List DeclarationId)
    (expr : Expression) (target : Binding) (state : State) (out : Outcome Flow) :
    Exec program available state (expr.body target) out ↔
      denoteBody program available (expr.body target) state = out :=
  exec_iff_denoteBody _ _ _ _ _

/-- Scratch staging leaves the denotation exactly unchanged across nested
positions, including any errors, heap mutations and existing iterator guards. -/
theorem Expression.lower_preserves (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (target : Binding) (state : State)
    (free : Lowering.ScratchFree state) (start : Nat := 0) :
    denoteBody program available (expr.lower target start) state =
      denoteBody program available (expr.body target) state :=
  ((Proofs.Languages.Starlark.Functions.Comprehensions.expression_exact
    program available expr admitted target start) state free).1.symm

/-- Exact checked-body agreement for assignment after scratch lowering. -/
theorem Expression.exec_iff_lowered (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (target : Binding) (state : State) (out : Outcome Flow)
    (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (expr.body target) out ↔
      denoteBody program available (expr.lower target start) state = out := by
  rw [expr.lower_preserves program available admitted target state free start]
  exact expr.exec_iff_denote program available target state out

/-- The exact denotation of scratch-lowered return code also characterizes
the independent return derivation of the direct code. -/
theorem Expression.exec_return_iff_lowered (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (state : State) (out : Outcome Flow)
    (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (expr.returnCode directStages) out ↔
      denoteBody program available (expr.returnCode (loweredStages start)) state = out := by
  rw [Proofs.Languages.Starlark.Functions.Comprehensions.return_exact program available expr admitted state free start]
  exact exec_iff_denoteBody _ _ _ _ _

/-- After the test has evaluated and been classified, only the selected
branch contributes to the final outcome or heap. -/
theorem conditional_selects (program : Program) (available : List DeclarationId)
    (stages : ExpressionStages) (test yes no : Expression) (target : Binding) (state next : State)
    (value : Lists.Value) (flag : Bool)
    (ran : denoteBody program available (test.compile stages expressionSlot) state = .ok .next next)
    (saved : denote (readSaved expressionSlot) next = .ok value next)
    (tested : truth value next = .ok flag next) :
    denoteBody program available ((Expression.branch test yes no).compile stages target) state =
      completeCall state (some target)
        (denoteBody program available
          (.seq ((if flag then yes else no).compile stages expressionSlot) (returnSaved expressionSlot)) next) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.conditional_selects
    program available stages test yes no target state next value flag ran saved tested

/-- A short circuit returns the original left value and keeps its effects.
The right-hand expression contributes no allocations or errors. -/
theorem logical_skips (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (op : LogicalOp) (left right : Expression) (target : Binding) (state next : State)
    (value : Lists.Value) (flag : Bool)
    (ran : denoteBody program available (left.compile stages expressionSlot) state = .ok .next next)
    (saved : denote (readSaved expressionSlot) next = .ok value next)
    (tested : truth value next = .ok flag next)
    (skip : (if op = .and then flag else !flag) = false) :
    denoteBody program available ((Expression.logical op left right).compile stages target) state =
      .ok .next ((restoreCaller state next).write target value) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.logical_skips
    program available stages op left right target state next value flag ran saved tested skip

/-- A failing callee expression skips all argument stages. -/
theorem callee_failure (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (callee : Lowering.Expr) (arguments : List Expression) (target : Binding)
    (state stopped : State) (error : Lists.Error)
    (failed : denoteBody program available (stages.plain (argumentSlot 0) callee) state = .error error stopped) :
    denoteBody program available ((Expression.callPos callee arguments).compile stages target) state =
      .error error (restoreCaller state stopped) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.callee_failure
    program available stages callee arguments target state stopped error failed

/-- The callee runs before the operand stages. The terminal call reads
the saved operands and uses the existing expansion and invocation rules. -/
theorem call_order (program : Program) (available : List DeclarationId) (target : Binding)
    (callee : Body) (shape : ArgumentShape) (operands : List (Binding → Body)) (state : State) :
    denoteBody program available (compileCall target callee shape operands) state =
      completeCall state (some target)
        (Outcome.resume (denoteBody program available callee state) fun
          | .next => denoteBody program available
              (stageArguments 1 operands fun saved =>
                .seq (.call (some expressionSlot) (readSaved (argumentSlot 0)) (Lowering.fillArguments shape saved))
                  (returnSaved expressionSlot))
          | signal => pure signal) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.call_order program available target callee shape operands state

/-- A failing comprehension-containing callee skips every argument group. -/
theorem call_callee_failure (program : Program) (available : List DeclarationId) (stages : ExpressionStages)
    (callee : Expression) (positional : List Expression) (keywords : List (String × Expression))
    (star starStar : Option Expression) (target : Binding) (state stopped : State) (error : Lists.Error)
    (failed : denoteBody program available (callee.compile stages (argumentSlot 0)) state = .error error stopped) :
    denoteBody program available ((Expression.call callee positional keywords star starStar).compile stages target) state =
      .error error (restoreCaller state stopped) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.call_callee_failure
    program available stages callee positional keywords star starStar target state stopped error failed

/-- Each argument stage runs once, and a failed stage contributes its
exact error and state without entering any later stage or dispatch. -/
theorem argument_order (program : Program) (available : List DeclarationId) (index : Nat)
    (first : Binding → Body) (rest : List (Binding → Body))
    (dispatch : List Lists.Expr → Body) (state : State) :
    denoteBody program available (stageArguments index (first :: rest) dispatch) state =
      Outcome.resume (denoteBody program available (first (argumentSlot index)) state) fun
      | .next => denoteBody program available
          (stageArguments (index + 1) rest fun saved => dispatch (readSaved (argumentSlot index) :: saved))
      | signal => pure signal :=
  Proofs.Languages.Starlark.Functions.Comprehensions.argument_order program available index first rest dispatch state

end Silmaril.Languages.Starlark.Functions.Comprehensions
