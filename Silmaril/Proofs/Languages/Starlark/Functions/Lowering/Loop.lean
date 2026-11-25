module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Preservation
public import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration

private theorem acquireAction (value : Value) : FrameAction (acquireIterator value) := by
  cases value with
  | list => exact actionMap _ (actionMap _ (actionList _))
  | tuple => exact actionMap _ (actionMap _ (actionTuple _))
  | dict => exact actionMap _ (actionMap _ (actionDict _))
  | range => exact actionPure _
  | _ => exact actionMap _ (actionThrow _)

private theorem enterMatch {s t : State} (same : StateMatch 0 s t) (guard : Option Address) :
    StateMatch 0 (enterIterator s guard) (enterIterator t guard) := by
  cases guard with
  | none => exact same
  | some address =>
    exact ⟨same.heap, congrArg (address :: ·) same.iterators, same.slots, same.bindings⟩

private theorem restoreMatch {source lowered : Outcome Flow} (same : OutcomeMatch 0 source lowered)
    {original saved : List Address} (stack : original = saved) :
    OutcomeMatch 0 (restoreIterators original source) (restoreIterators saved lowered) := by
  cases same with
  | ok related => exact .ok ⟨related.heap, stack, related.slots, related.bindings⟩
  | error related => exact .error ⟨related.heap, stack, related.slots, related.bindings⟩

private theorem writeBindingsMatch {s t : State} (same : StateMatch 0 s t)
    (assignments : List (Binding × Value)) :
    StateMatch 0 (writeBindings s assignments) (writeBindings t assignments) := by
  induction assignments generalizing s t with
  | nil => exact same
  | cons assignment rest ih =>
    obtain ⟨name, value⟩ := assignment
    exact ih (StateMatch.write same name value)

private theorem bindTargetMatch (target : LoopTarget) (value : Value) {s t : State}
    (same : StateMatch 0 s t) : OutcomeMatch 0 (bindTarget target value s) (bindTarget target value t) := by
  cases target with
  | name name => exact .ok (StateMatch.write same name value)
  | unpack bindings =>
    have acquired := frameRun (acquireAction value).1 same
    have kept := (acquireAction value).2 s
    simp only [bindTarget]
    rw [acquired]
    cases read : acquireIterator value s with
    | error error next =>
      rw [read] at kept
      exact .error (scopeTransport same kept)
    | ok iterator next =>
      rw [read] at kept
      obtain ⟨_, cursor⟩ := iterator
      have related := scopeTransport same kept
      change StateMatch 0 next (rebind next t.bindings) at related
      by_cases size : cursor.remaining = bindings.length
      · simpa [mapFrame, size] using OutcomeMatch.ok (value := ())
          (writeBindingsMatch related (bindings.zip cursor.collect))
      · simpa [mapFrame, size] using OutcomeMatch.error
          (error := .unpackArity bindings.length cursor.remaining) related

private theorem cursorMatch (sourceBody loweredBody : Meaning Flow)
    (bodyMatch : ∀ s t, StateMatch 0 s t → OutcomeMatch 0 (sourceBody s) (loweredBody t))
    (target : LoopTarget) (cursor : Cursor) (s t : State) (same : StateMatch 0 s t) :
    OutcomeMatch 0 (denoteCursor target sourceBody cursor s) (denoteCursor target loweredBody cursor t) := by
  rw [denoteCursor.eq_def target sourceBody cursor s, denoteCursor.eq_def target loweredBody cursor t]
  cases step : cursor.advance with
  | none => exact .ok same
  | some item =>
    obtain ⟨value, rest⟩ := item
    dsimp only
    have bound := bindTargetMatch target value same
    generalize bindTarget target value s = source at bound ⊢
    generalize bindTarget target value t = lowered at bound ⊢
    cases bound with
    | error next => exact .error next
    | ok afterBind =>
      rename_i boundValue u v
      cases boundValue
      simp only [Outcome.resume]
      have related := bodyMatch _ _ afterBind
      generalize sourceBody u = source at related ⊢
      generalize loweredBody v = lowered at related ⊢
      cases related with
      | ok next =>
        rename_i flow s' t'
        cases flow with
        | next | continueLoop => exact cursorMatch sourceBody loweredBody bodyMatch target rest s' t' next
        | breakLoop | returned _ => exact .ok next
      | error next => exact .error next
termination_by cursor.remaining
decreasing_by all_goals exact Cursor.advance_decreases step

private theorem forInMatch (sourceBody loweredBody : Meaning Flow)
    (bodyMatch : ∀ s t, StateMatch 0 s t → OutcomeMatch 0 (sourceBody s) (loweredBody t))
    (target : LoopTarget) (value : Value) {s t : State} (same : StateMatch 0 s t) :
    OutcomeMatch 0 (denoteForIn target sourceBody (.ok value s))
      (denoteForIn target loweredBody (.ok value t)) := by
  have acquired := frameRun (acquireAction value).1 same
  have kept := (acquireAction value).2 s
  simp only [denoteForIn, Outcome.resume]
  rw [acquired]
  cases read : acquireIterator value s with
  | error error next =>
    rw [read] at kept
    exact .error (scopeTransport same kept)
  | ok iterator next =>
    rw [read] at kept
    obtain ⟨guard, cursor⟩ := iterator
    have related := scopeTransport same kept
    exact restoreMatch
      (cursorMatch sourceBody loweredBody bodyMatch target cursor _ _ (enterMatch related guard)) related.iterators

theorem preservesForIn {program : Program} {available : List DeclarationId} {state : State}
    {iterable : Languages.Starlark.Functions.Lowering.Expr} {out : Outcome Value}
    (ran : Evaluates program available state iterable out) (free : ScratchFree state)
    (target : LoopTarget) (sourceBody loweredBody : Body)
    (bodyMatch : ∀ s t, StateMatch 0 s t → OutcomeMatch 0
      (denoteBody program available sourceBody s) (denoteBody program available loweredBody t))
    (start : Nat) :
    OutcomeMatch 0 (denoteBody program available (.forInExpr target iterable sourceBody) state)
      (denoteBody program available (lowerForIn target iterable loweredBody start).code state) := by
  have staged := stage_preserves ran free start
  rw [denoteBody]
  change OutcomeMatch 0 (denoteForIn target (denoteBody program available sourceBody)
    (denoteExpr program available iterable state)) _
  rw [denoteExpr_eq_of_evaluates ran]
  simp only [lowerForIn]
  cases out with
  | error error s =>
    obtain ⟨final, evaluated, similar⟩ := staged
    rw [denoteBody, evaluated]
    exact .error similar
  | ok value s =>
    obtain ⟨final, evaluated, similar, saved⟩ := staged
    rw [denoteBody, evaluated]
    change OutcomeMatch 0 _ (denoteBody program available
      (.forIn target (.read (.bound (temporary start))) loweredBody) final)
    rw [denoteBody]
    change OutcomeMatch 0 _ (denoteForIn target (denoteBody program available loweredBody)
      (denote (scratchRead start) final))
    rw [saved]
    exact forInMatch _ _ bodyMatch target value similar

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
