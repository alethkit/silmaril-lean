module

public import Silmaril.Languages.Starlark.Frontend.Module.Defs
import all Silmaril.Languages.Starlark.Frontend.Module.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Frontend.Module

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Frontend
open Silmaril.Languages.Starlark.Frontend.Module (lowerNamedArguments lowerArgument lowerSpread lowerCall LoweredCall callShape)

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

private theorem listMapM_length {α β ε : Type} {f : α → Except ε β} {input : List α}
    {output : List β} (mapped : input.mapM f = .ok output) : output.length = input.length := by
  induction input generalizing output with
  | nil => cases mapped; rfl
  | cons head rest ih =>
    rw [List.mapM_cons] at mapped
    cases first : f head with
    | error _ => simp [first, bind, Except.bind] at mapped
    | ok value =>
      cases tail : rest.mapM f with
      | error _ => simp [first, tail, bind, Except.bind] at mapped
      | ok values =>
        simp [first, tail, bind, Except.bind, pure, Except.pure] at mapped
        subst output
        simp [ih tail]

private theorem optionMapM_isSome {α β ε : Type} {f : α → Except ε β} {input : Option α}
    {output : Option β} (mapped : input.mapM f = .ok output) : output.isSome = input.isSome := by
  cases input with
  | none => cases mapped; rfl
  | some value =>
    cases result : f value <;> rw [Option.mapM, result] at mapped <;> cases mapped
    rfl

theorem lowerCall_operands {callee : String} {arguments : LocatedCallArguments}
    {result : LoweredCall} (lowering : lowerCall callee arguments = .ok result) :
    ∃ positional named star starStar,
      result.expression = .call (.scalar (.read callee)) positional named star starStar ∧
      result.spans = arguments.spans ∧
      callShape result.spans = Functions.Lowering.argumentShape positional named star starStar := by
  unfold lowerCall at lowering
  cases positions : arguments.positional.mapM lowerArgument with
  | error _ => simp [positions, bind, Except.bind] at lowering
  | ok positional =>
    simp only [positions, bind, Except.bind] at lowering
    cases names : lowerNamedArguments arguments.named with
    | error _ => simp [names] at lowering
    | ok named =>
      simp only [names] at lowering
      cases spread : arguments.star.mapM lowerSpread with
      | error _ => simp [spread] at lowering
      | ok star =>
        simp only [spread] at lowering
        cases mapping : arguments.starStar.mapM lowerSpread with
        | error _ => simp [mapping] at lowering
        | ok starStar =>
          simp [mapping, pure, Except.pure] at lowering
          subst result
          refine ⟨positional, named, star, starStar, rfl, rfl, ?_⟩
          simp [callShape, Functions.Lowering.argumentShape, LocatedCallArguments.spans, listMapM_length positions,
            lowerNamedArguments_names names, optionMapM_isSome spread, optionMapM_isSome mapping]

end Silmaril.Proofs.Languages.Starlark.Frontend.Module
