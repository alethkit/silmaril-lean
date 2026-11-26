module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
import all Silmaril.Languages.Starlark.Frontend.Module.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Frontend.Module

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Frontend
open Silmaril.Languages.Starlark.Frontend.Module (lowerNamedArguments lowerArgument)

theorem lowerNamedArguments_names {arguments : List LocatedNamedArgument}
    {lowered : List (String × Functions.Lowering.Resolve.SourceExpr)}
    (lowering : lowerNamedArguments arguments = .ok lowered) :
    lowered.map Prod.fst = arguments.map LocatedNamedArgument.name := by
  induction arguments generalizing lowered with
  | nil => cases lowering; rfl
  | cons argument rest ih =>
    have foldTail : (rest.mapM fun item => do
        return (item.name, ← lowerArgument item.value)) = lowerNamedArguments rest := rfl
    unfold lowerNamedArguments at lowering
    rw [List.mapM_cons, foldTail] at lowering
    cases value : lowerArgument argument.value with
    | error _ => simp [value, bind, Except.bind] at lowering
    | ok expr =>
      cases tail : lowerNamedArguments rest with
      | error _ => simp [value, bind, Except.bind, tail, pure, Except.pure] at lowering
      | ok result =>
        simp [value, bind, Except.bind, tail, pure, Except.pure] at lowering
        subst lowered
        simp [ih tail]

end Silmaril.Proofs.Languages.Starlark.Frontend.Module
