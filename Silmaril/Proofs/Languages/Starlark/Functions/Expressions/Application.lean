module

public import Silmaril.Languages.Starlark.Functions.Builtins.Thms
public import Silmaril.Languages.Starlark.Functions.Expressions.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Expressions.Operational.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Expressions

open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)

theorem expands_eq {state : State} {args : EvaluatedArguments} {out : Outcome Actual}
    (h : Expands args state out) : args.expand state = out := by
  cases h <;> simp_all [EvaluatedArguments.expand, bind, EStateM.bind, pure, EStateM.pure]

private theorem expands_denote (state : State) (args : EvaluatedArguments) :
    Expands args state (args.expand state) := by
  unfold EvaluatedArguments.expand
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  cases mapping : expandStarStar args.starStar state with
  | error error next => exact .mappingError mapping
  | ok keys next =>
    dsimp only
    cases spread : expandStar args.star next with
    | error error final => exact .spreadError mapping spread
    | ok values final => exact .success mapping spread

private theorem dispatch_eq {program : Program} {available : List DeclarationId} {state : State}
    {callee : Value} {actual : Actual} {out : Outcome Value}
    {calls : ClosureRuns available} {bodyMeaning : ClosureMeaning available}
    (closureEq : ∀ plan state out, calls plan state out → bodyMeaning plan state = out)
    (h : DispatchesWith program available calls state callee actual out) :
    denoteDispatchWith program available bodyMeaning callee actual state = out := by
  cases h with
  | reject prepared => simp only [denoteDispatchWith, prepared]
  | builtin prepared ran => simp only [denoteDispatchWith, prepared, (Builtins.invokes_iff_invoke _ _ _ _).mp ran]
  | returned prepared ran => simp only [denoteDispatchWith, prepared, closureEq _ _ _ ran]
  | failed prepared ran => simp only [denoteDispatchWith, prepared, closureEq _ _ _ ran]

private theorem dispatch_denote (program : Program) (available : List DeclarationId)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    (closureComplete : ∀ plan state, calls plan state (bodyMeaning plan state))
    (state : State) (callee : Value) (actual : Actual) :
    DispatchesWith program available calls state callee actual (denoteDispatchWith program available bodyMeaning callee actual state) := by
  unfold denoteDispatchWith
  cases prepared : prepareExpanded program available actual callee state with
  | error error next => exact .reject prepared
  | ok plan next =>
    cases plan with
    | builtin id bound => exact .builtin prepared ((Builtins.invokes_iff_invoke _ _ _ _).mpr rfl)
    | closure plan =>
      dsimp only
      have ran := closureComplete plan next
      cases body : bodyMeaning plan next with
      | ok flow final => exact .returned prepared (body ▸ ran)
      | error error final => exact .failed prepared (body ▸ ran)

theorem application_eq {program : Program} {available : List DeclarationId} {shape : ArgumentShape}
    {state : State} {values : List Value} {out : Outcome Value}
    {calls : ClosureRuns available} {bodyMeaning : ClosureMeaning available}
    (closureEq : ∀ plan state out, calls plan state out → bodyMeaning plan state = out)
    (h : AppliesWith program available calls shape state values out) :
    denoteApplicationWith program available bodyMeaning shape values state = out := by
  cases h with
  | expansionError expanded => simp only [denoteApplicationWith, bind, EStateM.bind, expands_eq expanded]
  | expanded expanded ran =>
    simp only [denoteApplicationWith, bind, EStateM.bind, expands_eq expanded, dispatch_eq closureEq ran]

theorem application_denote (program : Program) (available : List DeclarationId) (shape : ArgumentShape)
    (calls : ClosureRuns available) (bodyMeaning : ClosureMeaning available)
    (closureComplete : ∀ plan state, calls plan state (bodyMeaning plan state))
    (state : State) (callee : Value) (operands : List Value) :
    AppliesWith program available calls shape state (callee :: operands)
      (denoteApplicationWith program available bodyMeaning shape (callee :: operands) state) := by
  simp only [denoteApplicationWith, bind, EStateM.bind]
  have expanded := expands_denote state (shape.collect operands)
  cases expansion : (shape.collect operands).expand state with
  | error error next => exact .expansionError (expansion ▸ expanded)
  | ok actual next => exact .expanded (expansion ▸ expanded) (dispatch_denote program available calls bodyMeaning closureComplete next callee actual)

end Silmaril.Proofs.Languages.Starlark.Functions.Expressions
