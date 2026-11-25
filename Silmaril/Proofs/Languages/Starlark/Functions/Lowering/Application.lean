module

public import Silmaril.Languages.Starlark.Functions.Builtins.Thms
public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Source.Defs
public import Silmaril.Languages.Starlark.Functions.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists

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
    (h : Dispatches program available state callee actual out) :
    denoteDispatch program available callee actual state = out := by
  cases h with
  | reject prepared => simp only [denoteDispatch, prepared]
  | builtin prepared ran => simp only [denoteDispatch, prepared, (Builtins.invokes_iff_invoke _ _ _ _).mp ran]
  | returned prepared ran => simp only [denoteDispatch, prepared, (exec_iff_denoteBody _ _ _ _ _).mp ran]
  | failed prepared ran => simp only [denoteDispatch, prepared, (exec_iff_denoteBody _ _ _ _ _).mp ran]

private theorem dispatch_denote (program : Program) (available : List DeclarationId)
    (state : State) (callee : Value) (actual : Actual) :
    Dispatches program available state callee actual (denoteDispatch program available callee actual state) := by
  unfold denoteDispatch
  cases prepared : prepareExpanded program available actual callee state with
  | error error next => exact .reject prepared
  | ok plan next =>
    cases plan with
    | builtin id bound => exact .builtin prepared ((Builtins.invokes_iff_invoke _ _ _ _).mpr rfl)
    | closure plan =>
      dsimp only
      have ran := (exec_iff_denoteBody program (withoutDeclaration available plan.id) plan.body next _).mpr rfl
      cases body : denoteBody program (withoutDeclaration available plan.id) plan.body next with
      | ok flow final => exact .returned prepared (body ▸ ran)
      | error error final => exact .failed prepared (body ▸ ran)

theorem application_eq {program : Program} {available : List DeclarationId} {shape : ArgumentShape}
    {state : State} {values : List Value} {out : Outcome Value}
    (h : Applies program available shape state values out) :
    denoteApplication program available shape values state = out := by
  cases h with
  | expansionError expanded => simp only [denoteApplication, bind, EStateM.bind, expands_eq expanded]
  | expanded expanded ran =>
    simp only [denoteApplication, bind, EStateM.bind, expands_eq expanded, dispatch_eq ran]

theorem application_denote (program : Program) (available : List DeclarationId) (shape : ArgumentShape)
    (state : State) (callee : Value) (operands : List Value) :
    Applies program available shape state (callee :: operands)
      (denoteApplication program available shape (callee :: operands) state) := by
  simp only [denoteApplication, bind, EStateM.bind]
  have expanded := expands_denote state (shape.collect operands)
  cases expansion : (shape.collect operands).expand state with
  | error error next => exact .expansionError (expansion ▸ expanded)
  | ok actual next => exact .expanded (expansion ▸ expanded) (dispatch_denote program available next callee actual)

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
