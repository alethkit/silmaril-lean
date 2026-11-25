module

public import Silmaril.Languages.Starlark.Modules.Resolve.Assignment.Defs
public import Silmaril.Languages.Starlark.Functions.Comprehensions.Expression.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Assignment

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Assignment

open Functions (Program DeclarationId Exec denoteBody)
open Functions.Comprehensions (AssignmentPattern assignPatternCode directStages loweredStages)
open Functions.Lowering.Resolve (resolveTracked)
open Lists (Outcome State)
open Lists.Iteration (Flow)

local notation "SourceOperand" => Functions.Lowering.Resolve.SourceExpr
local notation "ResolvedOperand" => Functions.Lowering.Expr

/-- Successful shape analysis collects just the identifier leaves, in source order. -/
theorem parseAssignmentPattern_sound (scope : Scope) (target : SourceOperand)
    (result : AssignmentPattern SourceOperand × List String)
    (ran : parseAssignmentPattern (fun name => ⟨scope, name⟩) target = .ok result) :
    TargetShape scope target result :=
  Proofs.Languages.Starlark.Modules.Resolve.Assignment.shape_sound scope target result ran

/-- Successful bounded operand resolution gives exactly the ordered binding reads. -/
theorem resolveOperand_sound (block : LexicalBlock) {source : SourceOperand}
    (profile : OperandInProfile source) {value : ResolvedOperand} {reads : List Binding}
    (ran : resolveTracked block.context source = .ok (value, reads)) :
    OperandResolves block source value reads :=
  Proofs.Languages.Starlark.Modules.Resolve.Assignment.operand_sound block profile ran

/-- Target correctness for the assignment phase used by the mixed branch.
The profile hypothesis concerns only the shape and syntax of the target. -/
theorem target_sound (block : LexicalBlock) (scope : Scope) (target : SourceOperand) (rhs : CompExpr)
    (program next : Program) (result : ResolvedPatternAssignment)
    (profile : TargetInProfile scope target)
    (ran : elaboratePatternAssignment block.context scope target rhs program = .ok (result, next)) :
    TargetResolves block scope target result.pattern result.names result.targetReads :=
  Proofs.Languages.Starlark.Modules.Resolve.Assignment.target_sound block scope target rhs program next result
    profile ran

/-- Both parts of an accepted assignment relate to independent source rules.
The bounded RHS forms leave the declaration table unchanged. -/
theorem assignment_sound (block : LexicalBlock) (scope : Scope) (target : SourceOperand) (rhs : CompExpr)
    (program next : Program) (result : ResolvedPatternAssignment)
    (targetProfile : TargetInProfile scope target)
    (rhsProfile : RhsInProfile rhs)
    (ran : elaboratePatternAssignment block.context scope target rhs program = .ok (result, next)) :
    AssignmentResolves block scope target rhs result ∧ next = program :=
  Proofs.Languages.Starlark.Modules.Resolve.Assignment.assignment_sound block scope target rhs program next result
    targetProfile rhsProfile ran

/-- For a declaratively related assignment, the existing checked rules and
scratch denotation agree on the complete runtime outcome. Runtime admission
and the initial scratch invariant are supplied by the calling context. -/
theorem exec_iff_lowered_of_elaboration (block : LexicalBlock) (scope : Scope)
    (target : SourceOperand) (rhs : CompExpr) (program next : Program) (result : ResolvedPatternAssignment)
    (targetProfile : TargetInProfile scope target)
    (rhsProfile : RhsInProfile rhs)
    (ran : elaboratePatternAssignment block.context scope target rhs program = .ok (result, next))
    (available : List DeclarationId) (targetAdmitted : result.pattern.Admitted) (rhsAdmitted : result.rhs.Admitted)
    (state : State) (out : Outcome Flow) (free : Functions.Lowering.ScratchFree state) (start : Nat := 0) :
    AssignmentResolves block scope target rhs result ∧
      (Exec next available state (assignPatternCode result.pattern result.rhs directStages) out ↔
        denoteBody next available (assignPatternCode result.pattern result.rhs (loweredStages start)) state = out) :=
  ⟨(assignment_sound block scope target rhs program next result targetProfile rhsProfile ran).1,
    Functions.Comprehensions.exec_assignPattern_iff_lowered next available result.pattern result.rhs
      targetAdmitted rhsAdmitted state out free start⟩

end Silmaril.Languages.Starlark.Modules.Resolve.Assignment
