module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Atoms
public import Silmaril.Languages.Starlark.Functions.Builtins.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

private theorem packAction (signature : Signature) (bound : BoundArguments) :
    FrameAction (packArgs signature bound) := by
  cases varargs : signature.varargs <;> cases kwargs : signature.kwargs <;>
    simp only [packArgs, varargs, kwargs, pure_bind]
  · exact actionPure _
  · exact actionBind (actionAllocateDict _) fun _ => actionPure _
  · exact actionBind (actionAllocateTuple _) fun _ => actionPure _
  · exact actionBind (actionAllocateTuple _) fun _ =>
      actionBind (actionAllocateDict _) fun _ => actionPure _

private theorem builtinAction (id : Builtin) (actual : Actual) :
    FrameAction (Builtins.invoke id actual) := by
  have truthAction (value : Value) : FrameAction (Iteration.truth value) := by
    cases value with
    | list => exact actionMap _ (actionList _)
    | tuple => exact actionMap _ (actionTuple _)
    | dict => exact actionMap _ (actionDict _)
    | _ => exact actionPure _
  have itemsAction (id : Builtin) (value : Value) : FrameAction (Builtins.items id value) := by
    cases value with
    | list => exact actionMap Prod.snd (actionMap _ (actionList _))
    | tuple => exact actionMap Prod.snd (actionMap _ (actionTuple _))
    | dict => exact actionMap Prod.snd (actionMap _ (actionDict _))
    | _ => exact actionThrow _
  obtain ⟨positional, keywords⟩ := actual
  unfold Builtins.invoke
  cases keywords with
  | cons entry rest => cases entry; exact actionThrow _
  | nil =>
    cases positional with
    | nil =>
      cases id
      · exact actionPure _
      · exact actionThrow _
      · exact actionThrow _
      · exact actionAllocate _
      · exact actionAllocateTuple _
    | cons value rest =>
      cases rest with
      | cons => exact actionThrow _
      | nil =>
        cases id with
        | bool => exact actionMap _ (truthAction value)
        | len =>
          cases value <;> first | exact actionPure _ | exact actionMap _ (itemsAction _ _)
        | type => exact actionPure _
        | list => exact actionBind (itemsAction _ _) actionAllocate
        | tuple => exact actionBind (itemsAction _ _) actionAllocateTuple

private def transportPlan (bindings : Binding → Option Value) {available : List DeclarationId} :
    Outcome (CallPlan available) → Outcome (CallPlan available)
  | .ok (.closure plan) s => .ok (.closure plan) s
  | .ok (.builtin id actual) s => .ok (.builtin id actual) (rebind s bindings)
  | .error error s => .error error (rebind s bindings)

private theorem expand_positional (args : List Languages.Starlark.Lists.Expr) (values : List Value) (s : State) :
    (Arguments.expand { positional := args } values) s = .ok ⟨values.take args.length, []⟩ s := by
  simp [Arguments.expand, expandStarStar, expandStar, bind, EStateM.bind, pure, EStateM.pure]

private theorem prepare_positional (program : Program) (available : List DeclarationId)
    (args args' : List Languages.Starlark.Lists.Expr) (len : args.length = args'.length) (values : List Value) (s : State) :
    prepare program available { positional := args } values s =
      prepare program available { positional := args' } values s := by
  cases values with
  | nil => rfl
  | cons head tail =>
    simp only [prepare, bind, EStateM.bind, expand_positional, len]

private theorem prepare_frame (program : Program) (available : List DeclarationId)
    (args : List Languages.Starlark.Lists.Expr) (values : List Value) (s : State) (f : Binding → Option Value) :
    prepare program available { positional := args } values (rebind s f) =
      transportPlan f (prepare program available { positional := args } values s) := by
  cases values with
  | nil => rfl
  | cons callee values =>
    simp only [prepare, bind, EStateM.bind, expand_positional]
    cases callee with
    | function address =>
      dsimp only [EStateM.bind]
      have get := frameProject address (fun | .function c => some c | _ => none) s f
      change getClosure address (rebind s f) = mapFrame (rebind · f) (getClosure address s) at get
      rw [get]
      cases getClosure address s with
      | error => rfl
      | ok closure u =>
        dsimp only [mapFrame]
        cases program[closure.declaration]? with
        | none => rfl
        | some declaration =>
          by_cases permitted : closure.declaration ∈ available
          · simp only [dite_eq_left permitted, EStateM.bind]
            let bound := bindArguments declaration.signature closure.defaults ⟨values.take args.length, []⟩
            have kept := frameFromExcept bound u f
            change fromExcept bound (rebind u f) = _ at kept
            rw [kept]
            cases fromExcept bound u with
            | error => rfl
            | ok assigned v =>
              simp only [mapFrame]
              rw [(packAction declaration.signature assigned).1 v f]
              cases packArgs declaration.signature assigned v <;> rfl
          · simp only [dite_eq_right permitted]
            rfl
    | _ => rfl

private theorem prepare_scope (program : Program) (available : List DeclarationId)
    (args : List Languages.Starlark.Lists.Expr) (values : List Value) (s : State) :
    match prepare program available { positional := args } values s with
    | .ok (.closure _) _ => True
    | .ok (.builtin _ _) t | .error _ t => SameScope t s := by
  cases values with
  | nil => exact ⟨rfl, rfl⟩
  | cons callee values =>
    simp only [prepare, bind, EStateM.bind, expand_positional]
    cases callee with
    | function address =>
      dsimp only [EStateM.bind]
      have kept := scopeProject address (fun | .function c => some c | _ => none) s
      change SameScope (finishState (getClosure address s)) s at kept
      cases he : getClosure address s with
      | error error next =>
        simpa only [he, finishState] using kept
      | ok closure next =>
        rw [he] at kept
        dsimp only
        cases entry : program[closure.declaration]? with
        | none => exact kept
        | some declaration =>
          by_cases permitted : closure.declaration ∈ available
          · simp only [dite_eq_left permitted]
            simp only [EStateM.bind]
            cases boundResult : bindArguments declaration.signature closure.defaults ⟨values.take args.length, []⟩ with
            | error => exact kept
            | ok bound =>
              simp only [fromExcept, pure, EStateM.pure]
              have packed := (packAction declaration.signature bound).2 next
              cases hp : packArgs declaration.signature bound next with
              | error err final =>
                rw [hp] at packed
                exact ⟨packed.1.trans kept.1, packed.2.trans kept.2⟩
              | ok => trivial
          · simp only [dite_eq_right permitted]
            exact kept
    | _ => exact ⟨rfl, rfl⟩

theorem applies_scope {program : Program} {available : List DeclarationId} {arity : Nat}
    {s : State} {values : List Value} {out : Outcome Value}
    (h : Applies program available arity s values out) : SameScope (finishState out) s := by
  have kept := prepare_scope program available (positionalShape arity).positional values s
  change (match prepare program available (positionalShape arity) values s with
    | .ok (.closure _) _ => True
    | .ok (.builtin _ _) t | .error _ t => SameScope t s) at kept
  cases h with
  | reject rejected => simpa only [rejected, finishState] using kept
  | @builtin id actual next out prepared invoked =>
    rw [prepared] at kept
    have evaluated := (Builtins.invokes_iff_invoke _ _ _ _).mp invoked
    have run := (builtinAction id actual).2 next
    rw [evaluated] at run
    exact ⟨run.1.trans kept.1, run.2.trans kept.2⟩
  | returned | failed => exact ⟨rfl, rfl⟩

@[expose] def commit (target : Binding) : Outcome Value → Outcome Flow
  | .ok value s => .ok .next (s.write target value)
  | .error error s => .error error s

theorem lower_call {program : Program} {available : List DeclarationId} {arity : Nat}
    {s t : State} {values : List Value} {out : Outcome Value}
    (h : Applies program available arity s values out)
    (same : StateMatch 0 s t) (target : Binding) (callee : Languages.Starlark.Lists.Expr) (args : List Languages.Starlark.Lists.Expr)
    (arityEq : args.length = arity)
    (readArgs : denote (Arguments.operands callee { positional := args }) t = .ok values t) :
    denoteBody program available (.call (some target) callee { positional := args }) t =
      commit target (mapFrame (rebind · t.bindings) out) := by
  have prep := prepare_frame program available args values s t.bindings
  rw [same_rebound same] at prep
  have arityMatch : args.length = (positionalShape arity).positional.length := by
    simp [positionalShape, arityEq]
  have posEq := prepare_positional program available args (positionalShape arity).positional arityMatch values s
  change prepare program available { positional := args } values s =
    prepare program available (positionalShape arity) values s at posEq
  have prep := prep.trans (congrArg (transportPlan t.bindings) posEq)
  rw [denoteBody, readArgs, Outcome.resume, prep]
  cases h with
  | reject rejected => simp only [rejected, transportPlan, mapFrame, commit]
  | builtin prepared invoked =>
    rw [prepared]
    simp only [transportPlan]
    have executed := (Builtins.invokes_iff_invoke _ _ _ _).mp invoked
    rw [(builtinAction _ _).1, executed]
    cases out <;> rfl
  | @returned plan next final flow prepared ran =>
    rw [prepared]
    simp only [transportPlan, (exec_iff_denoteBody _ _ _ _ _).mp ran]
    cases flow <;>
      simp [completeCall, writeCallResult, commit, mapFrame, rebind, restoreCaller, ← same.slots, callValue]
  | failed prepared ran =>
    rw [prepared]
    simp only [transportPlan, (exec_iff_denoteBody _ _ _ _ _).mp ran]
    simp [completeCall, commit, mapFrame, rebind, restoreCaller, ← same.slots]

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
