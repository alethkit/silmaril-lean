module

public import Silmaril.Languages.PythonStarlark.ClosedReturn.Defs
import Silmaril.Proofs.Languages.PythonStarlark.ClosedReturn.Agreement

public section

namespace Silmaril.Languages.PythonStarlark.ClosedReturn

open Semantics.Operational

variable {observation : Observation}

/-- The common integer fragment always has an arithmetic-profile Python entry. -/
theorem int_admitted (body : IntBody) :
    Python.Core.Profile.arithmetic.supports body.python.value :=
  Proofs.Languages.PythonStarlark.ClosedReturn.python_admitted id body.value

theorem int_resolves (body : IntBody) :
    Starlark.resolveFunctionBody [] [] body.starlark = .ok (.ret (some (body.value.starlark .int))) :=
  Proofs.Languages.PythonStarlark.ClosedReturn.int_resolves body

theorem numeric_admitted (body : NumericBody) :
    Python.Core.Profile.arithmetic.supports body.python.value :=
  Proofs.Languages.PythonStarlark.ClosedReturn.python_admitted NumericLiteral.pythonInt body.body.value

theorem numeric_resolves (body : NumericBody) :
    Starlark.resolveFunctionBody [] [] body.starlark =
      .ok (.ret (some (body.body.value.starlark NumericLiteral.starlarkResolved))) :=
  Proofs.Languages.PythonStarlark.ClosedReturn.numeric_resolves body

theorem python_observes_iff {profile : Python.Core.Profile} {body : Python.Core.Body}
    (admitted : profile.supports body.value) :
    PythonObserves profile body observation ↔ observation = observePython (.returned body.value.eval) :=
  Proofs.Languages.PythonStarlark.ClosedReturn.python_observes_iff admitted

theorem starlark_observes_iff {body : Starlark.SourceStmt} :
    StarlarkObserves body observation ↔ observation = observeStarlark (Starlark.runFunctionBody [] [] body) :=
  Proofs.Languages.PythonStarlark.ClosedReturn.starlark_observes_iff

theorem starlark_observes_exec {body : Starlark.SourceStmt} {stmt : Starlark.ResolvedStmt}
    {result : Starlark.Result Starlark.Completion}
    (resolved : Starlark.resolveFunctionBody [] [] body = .ok stmt) (exec : Starlark.Exec {} stmt result) :
    StarlarkObserves body observation ↔ observation = observeStarlarkExec result :=
  Proofs.Languages.PythonStarlark.ClosedReturn.starlark_observes_exec resolved exec

/-- The scalar Starlark semantics supplies a finite derivation after resolution. -/
theorem starlark_total {stmt : Starlark.ResolvedStmt} (frame : Starlark.Frame) :
    ∃ result, Starlark.Exec frame stmt result :=
  Proofs.Languages.PythonStarlark.ClosedReturn.starlark_total frame

theorem starlark_no_divergence (body : Starlark.SourceStmt) : ¬ StarlarkObserves body .diverges :=
  Proofs.Languages.PythonStarlark.ClosedReturn.starlark_no_divergence body

/-- The integer fragment agrees on all observations, including absence of divergence. -/
theorem agree (body : IntBody) : Agree body :=
  Proofs.Languages.PythonStarlark.ClosedReturn.agree body

end Silmaril.Languages.PythonStarlark.ClosedReturn
