module

public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs
import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Denotation

public section

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State Outcome)

/-- Every operational derivation agrees with direct denotation on the exact
result or error and final state. -/
theorem denoteExpr_eq_of_evaluates {program : Program} {available : List DeclarationId}
    {state : State} {expression : Expr} {out : Outcome Lists.Value}
    (ran : Evaluates program available state expression out) :
    denoteExpr program available expression state = out :=
  Proofs.Languages.Starlark.Functions.Lowering.denote_eq_of_evaluates ran

/-- An expression with admissible atoms also has an operational derivation
for its denotational outcome. No initial heap or scratch-slot condition is needed. -/
theorem evaluates_iff_denoteExpr (program : Program) (available : List DeclarationId)
    {expression : Expr} (admitted : Admitted expression) (state : State) (out : Outcome Lists.Value) :
    Evaluates program available state expression out ↔ denoteExpr program available expression state = out :=
  ⟨denoteExpr_eq_of_evaluates,
    fun h => h ▸ Proofs.Languages.Starlark.Functions.Lowering.evaluates_denote program available admitted state⟩

end Silmaril.Languages.Starlark.Functions.Lowering
