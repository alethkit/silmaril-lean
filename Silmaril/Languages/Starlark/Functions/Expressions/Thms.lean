module

public import Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Expressions.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Functions.Expressions.Agreement

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)

/-- Operational expansion and executable expansion give the same outcome. -/
theorem expands_eq {state : State} {args : EvaluatedArguments} {out : Outcome Actual}
    (ran : Expands args state out) : args.expand state = out :=
  Proofs.Languages.Starlark.Functions.Expressions.expands_eq ran

/-- Soundness given exact agreement for each prepared closure invoked by the expression. -/
theorem denoteExprWith_eq_of_evaluates {program : Program} {available : List DeclarationId}
    {calls : ClosureRuns available} {bodyMeaning : ClosureMeaning available}
    {atomAllowed : Lists.Expr → Prop} {state : State} {expression : Expr} {out : Outcome Lists.Value}
    (closureEq : ∀ plan next result, calls plan next result → bodyMeaning plan next = result)
    (ran : EvaluatesWith program available calls atomAllowed state expression out) :
    denoteExprWith program available bodyMeaning expression state = out :=
  Proofs.Languages.Starlark.Functions.Expressions.denote_eq_of_evaluates closureEq ran

/-- Completeness when the atoms are admitted and each supplied closure denotation has a derivation. -/
theorem evaluatesWith_denote (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    (closureComplete : ∀ plan state, calls plan state (bodyMeaning plan state))
    {atomAllowed : Lists.Expr → Prop} {expression : Expr} (admitted : AdmittedWith atomAllowed expression)
    (state : State) :
    EvaluatesWith program available calls atomAllowed state expression
      (denoteExprWith program available bodyMeaning expression state) :=
  Proofs.Languages.Starlark.Functions.Expressions.evaluates_denote
    program available calls bodyMeaning closureComplete admitted state

/-- Ordered expression evaluation agrees on values or the first error and its state. -/
theorem denoteExprsWith_eq_of_evaluatesMany {program : Program} {available : List DeclarationId}
    {calls : ClosureRuns available} {bodyMeaning : ClosureMeaning available}
    {atomAllowed : Lists.Expr → Prop} {state : State} {expressions : List Expr}
    {out : Outcome (List Lists.Value)}
    (closureEq : ∀ plan next result, calls plan next result → bodyMeaning plan next = result)
    (ran : EvaluatesManyWith program available calls atomAllowed state expressions out) :
    expressions.mapM (denoteExprWith program available bodyMeaning) state = out :=
  Proofs.Languages.Starlark.Functions.Expressions.denote_eq_of_evaluatesMany closureEq ran

/-- Ordered expression evaluation has a derivation when its atoms and closure calls do. -/
theorem evaluatesManyWith_denote (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    (closureComplete : ∀ plan state, calls plan state (bodyMeaning plan state))
    {atomAllowed : Lists.Expr → Prop} (expressions : List Expr)
    (admitted : ∀ expression ∈ expressions, AdmittedWith atomAllowed expression) (state : State) :
    EvaluatesManyWith program available calls atomAllowed state expressions
      (expressions.mapM (denoteExprWith program available bodyMeaning) state) :=
  Proofs.Languages.Starlark.Functions.Expressions.evaluatesMany_denote
    program available calls bodyMeaning closureComplete expressions admitted state

/-- Embedding call-free operands as atoms preserves their old denotation. -/
theorem denote_atom_operands (program : Program) (available : List DeclarationId)
    (bodyMeaning : ClosureMeaning available) (operands : List Lists.Expr) (state : State) :
    (operands.map Expr.atom).mapM (denoteExprWith program available bodyMeaning) state =
      Lists.denote (operandList operands) state :=
  Proofs.Languages.Starlark.Functions.Expressions.denote_atom_operands program available bodyMeaning operands state

/-- Native body returns admit every call-free collection atom. -/
theorem admits_all_atoms (expression : Expr) : AdmittedWith (fun _ => True) expression :=
  Proofs.Languages.Starlark.Functions.Expressions.admits_all_atoms expression

end Silmaril.Languages.Starlark.Functions.Lowering
