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

/-- The binder receives the single RHS result after discarding private
bindings. An RHS error skips binding and retains the residual heap. -/
theorem Expression.denote_assignTarget (program : Program) (available : List DeclarationId)
    (expr : Expression) (target : Lists.Iteration.LoopTarget) (stages : ExpressionStages) (state : State) :
    denoteBody program available (expr.assignTargetCode target stages) state =
      match denoteBody program available (expr.returnCode stages) state with
      | .error error next => .error error (restoreCaller state next)
      | .ok (.returned value) next =>
        Outcome.resume (Lists.Iteration.bindTarget target value (restoreCaller state next)) fun () => pure .next
      | .ok signal next => .ok signal (restoreCaller state next) := by
  rw [Expression.assignTargetCode, denoteBody]
  rfl

/-- Scratch lowering preserves both RHS failure and any partial writes made
by the existing pattern binder. -/
theorem Expression.assignTarget_preserves (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (target : Lists.Iteration.LoopTarget)
    (state : State) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    denoteBody program available (expr.assignTargetCode target (loweredStages start)) state =
      denoteBody program available (expr.assignTargetCode target directStages) state :=
  Proofs.Languages.Starlark.Functions.Comprehensions.assign_target_exact
    program available expr admitted target state free start

/-- Independent checked-body derivations determine the exact scratch-lowered
outcome, including the frame, heap and iterator guards. -/
theorem Expression.exec_assignTarget_iff_lowered (program : Program) (available : List DeclarationId)
    (expr : Expression) (admitted : expr.Admitted) (target : Lists.Iteration.LoopTarget)
    (state : State) (out : Outcome Flow) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (expr.assignTargetCode target directStages) out ↔
      denoteBody program available (expr.assignTargetCode target (loweredStages start)) state = out := by
  rw [expr.assignTarget_preserves program available admitted target state free start]
  exact exec_iff_denoteBody _ _ _ _ _

/-- Lower the RHS and each reached store operand with the same exact outcome.
The residual state includes writes before any later unpack or store failure. -/
theorem assignPattern_preserves (program : Program) (available : List DeclarationId)
    (pattern : AssignmentPattern) (rhs : Expression) (targetAdmitted : pattern.Admitted)
    (rhsAdmitted : rhs.Admitted) (state : State) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    denoteBody program available (assignPatternCode pattern rhs (loweredStages start)) state =
      denoteBody program available (assignPatternCode pattern rhs directStages) state :=
  Proofs.Languages.Starlark.Functions.Comprehensions.assign_pattern_exact
    program available pattern rhs targetAdmitted rhsAdmitted state free start

theorem exec_assignPattern_iff_lowered (program : Program) (available : List DeclarationId)
    (pattern : AssignmentPattern) (rhs : Expression) (targetAdmitted : pattern.Admitted)
    (rhsAdmitted : rhs.Admitted) (state : State) (out : Outcome Flow)
    (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (assignPatternCode pattern rhs directStages) out ↔
      denoteBody program available (assignPatternCode pattern rhs (loweredStages start)) state = out := by
  rw [assignPattern_preserves program available pattern rhs targetAdmitted rhsAdmitted state free start]
  exact exec_iff_denoteBody _ _ _ _ _

/-- The assignment evaluates its RHS once and uses the saved value for
the whole pattern. The continuation runs only after RHS success. -/
theorem assignPattern_phases (program : Program) (available : List DeclarationId)
    (pattern : AssignmentPattern) (rhs : Expression) (stages : ExpressionStages) (state : State) :
    denoteBody program available (assignPatternCode pattern rhs stages) state =
      restoreTemporaryBindings [patternSlot 0 0] state
        (Outcome.resume (denoteBody program available (rhs.compile stages (patternSlot 0 0))
          (enterTemporaryBindings [patternSlot 0 0] state)) fun
          | .next => denoteBody program available (pattern.code stages (patternSlot 0 0) 1)
          | signal => pure signal) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.assign_pattern_phases program available pattern rhs stages state

/-- A failed RHS never reaches unpacking or a target leaf. -/
theorem assignPattern_rhs_failure (program : Program) (available : List DeclarationId)
    (pattern : AssignmentPattern) (rhs : Expression) (stages : ExpressionStages)
    (state failed : State) (error : Lists.Error)
    (ran : denoteBody program available (rhs.compile stages (patternSlot 0 0))
      (enterTemporaryBindings [patternSlot 0 0] state) = .error error failed) :
    denoteBody program available (assignPatternCode pattern rhs stages) state =
      restoreTemporaryBindings [patternSlot 0 0] state (.error error failed) := by
  rw [assignPattern_phases, ran] <;> rfl

/-- Scratch lowering of each staged operand leaves the exact assignment
outcome unchanged, including the heap, frame and iterator stack. -/
theorem setIndex_preserves (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (receiverAdmitted : receiver.Admitted)
    (subscriptAdmitted : subscript.Admitted) (rhsAdmitted : rhs.Admitted)
    (state : State) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    denoteBody program available (setIndexCode receiver subscript rhs (loweredStages start)) state =
      denoteBody program available (setIndexCode receiver subscript rhs directStages) state :=
  Proofs.Languages.Starlark.Functions.Comprehensions.set_index_exact
    program available receiver subscript rhs receiverAdmitted subscriptAdmitted rhsAdmitted state free start

/-- The checked-body derivation determines the exact scratch-lowered store outcome. -/
theorem exec_setIndex_iff_lowered (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (receiverAdmitted : receiver.Admitted)
    (subscriptAdmitted : subscript.Admitted) (rhsAdmitted : rhs.Admitted)
    (state : State) (out : Outcome Flow) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (setIndexCode receiver subscript rhs directStages) out ↔
      denoteBody program available (setIndexCode receiver subscript rhs (loweredStages start)) state = out := by
  rw [setIndex_preserves program available receiver subscript rhs receiverAdmitted subscriptAdmitted rhsAdmitted
    state free start]
  exact exec_iff_denoteBody _ _ _ _ _

/-- RHS failure skips the receiver, index and store and retains its effects. -/
theorem setIndex_rhs_failure (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (stages : ExpressionStages) (state failed : State) (error : Lists.Error)
    (ran : denoteBody program available (rhs.compile stages (argumentSlot 0)) state = .error error failed) :
    denoteBody program available (setIndexCode receiver subscript rhs stages) state =
      .error error (restoreCaller state failed) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.set_index_rhs_failure
    program available receiver subscript rhs stages state failed error ran

/-- Once the target operands succeed, read the old value before the RHS.
The remaining code uses the saved target values. A read error skips the RHS. -/
theorem addIndex_after_target (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (stages : ExpressionStages) (state afterReceiver afterIndex : State)
    (recv : denoteBody program available (receiver.compile stages (argumentSlot 0)) state =
      .ok .next afterReceiver)
    (index : denoteBody program available (subscript.compile stages (argumentSlot 1)) afterReceiver =
      .ok .next afterIndex) :
    denoteBody program available (addIndexCode receiver subscript rhs stages) state =
      completeCall state none (Outcome.resume (denoteBody program available readIndexForAdd afterIndex) fun
        | .next => denoteBody program available (.seq (rhs.compile stages (argumentSlot 3)) writeIndexSum)
        | signal => pure signal) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.add_index_after_target
    program available receiver subscript rhs stages state afterReceiver afterIndex recv index

/-- Scratch lowering preserves all operand, read, arithmetic and write
outcomes of the checked integer subscript addition. -/
theorem addIndex_preserves (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (receiverAdmitted : receiver.Admitted)
    (subscriptAdmitted : subscript.Admitted) (rhsAdmitted : rhs.Admitted)
    (state : State) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    denoteBody program available (addIndexCode receiver subscript rhs (loweredStages start)) state =
      denoteBody program available (addIndexCode receiver subscript rhs directStages) state :=
  Proofs.Languages.Starlark.Functions.Comprehensions.add_index_exact
    program available receiver subscript rhs receiverAdmitted subscriptAdmitted rhsAdmitted state free start

theorem exec_addIndex_iff_lowered (program : Program) (available : List DeclarationId)
    (receiver subscript rhs : Expression) (receiverAdmitted : receiver.Admitted)
    (subscriptAdmitted : subscript.Admitted) (rhsAdmitted : rhs.Admitted)
    (state : State) (out : Outcome Flow) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (addIndexCode receiver subscript rhs directStages) out ↔
      denoteBody program available (addIndexCode receiver subscript rhs (loweredStages start)) state = out := by
  rw [addIndex_preserves program available receiver subscript rhs receiverAdmitted subscriptAdmitted rhsAdmitted
    state free start]
  exact exec_iff_denoteBody _ _ _ _ _

/-- The same preservation applies to lexical name addition. -/
theorem addName_preserves (program : Program) (available : List DeclarationId)
    (target : Binding) (rhs : Expression) (admitted : rhs.Admitted)
    (state : State) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    denoteBody program available (addNameCode target rhs (loweredStages start)) state =
      denoteBody program available (addNameCode target rhs directStages) state :=
  Proofs.Languages.Starlark.Functions.Comprehensions.add_name_exact
    program available target rhs admitted state free start

theorem exec_addName_iff_lowered (program : Program) (available : List DeclarationId)
    (target : Binding) (rhs : Expression) (admitted : rhs.Admitted)
    (state : State) (out : Outcome Flow) (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (addNameCode target rhs directStages) out ↔
      denoteBody program available (addNameCode target rhs (loweredStages start)) state = out := by
  rw [addName_preserves program available target rhs admitted state free start]
  exact exec_iff_denoteBody _ _ _ _ _

/-- Replacing each admitted definition-time operand by scratch-lowered code
preserves the exact outcome and state of the complete definition. -/
theorem definition_defaults_preserved (program : Program) (available : List DeclarationId)
    (target : Binding) (id : DeclarationId) (defaults : List (Binding × Expression))
    (admitted : ∀ item ∈ defaults, item.2.Admitted) (state : State)
    (free : Lowering.ScratchFree state) (start : Nat := 0) :
    denoteBody program available (definitionWithDefaults (loweredStages start) target id defaults) state =
      denoteBody program available (definitionWithDefaults directStages target id defaults) state :=
  ((Proofs.Languages.Starlark.Functions.Comprehensions.definition_defaults_exact
    program available target id defaults admitted start) state free).1.symm

/-- The independent checked-body rules for a staged definition characterize
scratch-lowered execution, including errors, the heap and iterator guards. -/
theorem definition_exec_iff_lowered (program : Program) (available : List DeclarationId)
    (target : Binding) (id : DeclarationId) (defaults : List (Binding × Expression))
    (admitted : ∀ item ∈ defaults, item.2.Admitted) (state : State) (out : Outcome Flow)
    (free : Lowering.ScratchFree state) (start : Nat := 0) :
    Exec program available state (definitionWithDefaults directStages target id defaults) out ↔
      denoteBody program available (definitionWithDefaults (loweredStages start) target id defaults) state = out := by
  rw [definition_defaults_preserved program available target id defaults admitted state free start]
  exact exec_iff_denoteBody _ _ _ _ _

/-- A failed first default skips the remaining defaults and closure
installation. Its residual heap and iterator context survive frame restoration. -/
theorem definition_default_failure (program : Program) (available : List DeclarationId)
    (stages : ExpressionStages) (target parameter : Binding) (id : DeclarationId) (expr : Expression)
    (rest : List (Binding × Expression)) (state failed : State) (error : Lists.Error)
    (ran : denoteBody program available (expr.compile stages (defaultSlot parameter)) state =
      .error error failed) :
    denoteBody program available (definitionWithDefaults stages target id ((parameter, expr) :: rest)) state =
      .error error (restoreCaller state failed) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.definition_default_failure
    program available stages target parameter id expr rest state failed error ran

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

/-- A dictionary display runs the key, value and insertion in order.
A failure skips the rest of the entry and every later pair. -/
theorem display_entry_order (program : Program) (available : List DeclarationId)
    (key value : Binding → Body) (rest : Body) (state : State) :
    denoteBody program available (stageDisplayEntry key value rest) state =
      Outcome.resume (denoteBody program available (key (argumentSlot 0)) state) fun
        | .next => fun next =>
          Outcome.resume (denoteBody program available (value (argumentSlot 1)) next) fun
            | .next => fun next =>
              Outcome.resume (denoteBody program available
                (.insertDictEntry expressionSlot (argumentSlot 0) (argumentSlot 1)) next) fun
                | .next => denoteBody program available rest
                | signal => pure signal
            | signal => pure signal
        | signal => pure signal :=
  Proofs.Languages.Starlark.Functions.Comprehensions.display_entry_order program available key value rest state

/-- Subscript validation follows both successful operand evaluations.
Either operand can fail before indexing is attempted. -/
theorem index_order (program : Program) (available : List DeclarationId)
    (target : Binding) (receiver subscript : Binding → Body) (state : State) :
    denoteBody program available (compileIndex target receiver subscript) state =
      completeCall state (some target)
        (Outcome.resume (denoteBody program available (receiver (argumentSlot 0)) state) fun
          | .next => fun next =>
            Outcome.resume (denoteBody program available (subscript (argumentSlot 1)) next) fun
              | .next => denoteBody program available (.returnExpr
                  (.atom (.index (readSaved (argumentSlot 0)) (readSaved (argumentSlot 1)))))
              | signal => pure signal
          | signal => pure signal) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.index_order program available target receiver subscript state

/-- Evaluate the receiver, start, stop and stride before reading a slice.
The first failed stage keeps its effects and skips every later stage. -/
theorem slice_order (program : Program) (available : List DeclarationId)
    (target : Binding) (receiver start stop stride : Binding → Body) (state : State) :
    let saved := [0, 1, 2, 3].map fun index => readSaved (argumentSlot index)
    let readback := denoteBody program available (.returnExpr (.atom (.slice (operandList saved))))
    let stages := [receiver (argumentSlot 0), start (argumentSlot 1),
      stop (argumentSlot 2), stride (argumentSlot 3)].map (denoteBody program available)
    let execute := stages.foldr (fun operand rest next => Outcome.resume (operand next) fun
      | .next => rest
      | signal => pure signal) readback
    denoteBody program available (compileSequence target (.slice ∘ operandList) [receiver, start, stop, stride]) state =
      completeCall state (some target) (execute state) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.slice_order program available target receiver start stop stride state

/-- A failing first iterable leaves its effects and restores the caller.
The comprehension's lexical targets and first cursor are entered only after success. -/
theorem first_iterable_failure (program : Program) (available : List DeclarationId)
    (target : Binding) (privateSlots locals : List Binding) (first : Lists.Iteration.LoopTarget)
    (initial iterable rest : Body) (state ready stopped : Lists.State) (error : Lists.Error)
    (allocated : denoteBody program available initial
      ((resultSlot :: operandSlot :: privateSlots).foldl Lists.State.allocateSlot state) = .ok .next ready)
    (failed : denoteBody program available iterable ready = .error error stopped) :
    denoteBody program available (compileScopedWith target privateSlots locals first initial iterable rest) state =
      .error error (restoreCaller state stopped) :=
  Proofs.Languages.Starlark.Functions.Comprehensions.first_iterable_failure
    program available target privateSlots locals first initial iterable rest state ready stopped error allocated failed

/-- At a reached dictionary head, the key and value run before the shared
dictionary update. A failed key skips the value and either failure skips the update. -/
theorem dict_yield_order (program : Program) (available : List DeclarationId)
    (key value : Body) (state : State) :
    denoteBody program available (putYield key value) state =
      Outcome.resume (denoteBody program available key state) fun
        | .next => fun next =>
          Outcome.resume (denoteBody program available value next) fun
            | .next => denoteBody program available putResult
            | signal => pure signal
        | signal => pure signal :=
  Proofs.Languages.Starlark.Functions.Comprehensions.dict_yield_order program available key value state

end Silmaril.Languages.Starlark.Functions.Comprehensions
