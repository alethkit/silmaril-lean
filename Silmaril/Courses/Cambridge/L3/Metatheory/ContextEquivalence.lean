module

public import Silmaril.Courses.Cambridge.L3.EvaluationContexts
public import Silmaril.Courses.Cambridge.L3.Reduction
public import Silmaril.Courses.Cambridge.L3.Typing

/-! # Relating the L3 context and direct rules

Theorem 26 compares the two presentations. Section 5.4 prints `v := □`.
The direct rule (assign2) in §5.5 requires `ℓ := □`. A well-typed value
on the left of an assignment must be a location. With the location premise
on the frame, equivalence also holds on arbitrary configurations.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

theorem Compute.toStep {before after : Config} (compute : Compute before after) :
    Step before after := by
  cases compute with
  | add l r s => exact .add l r s
  | ge l r s => exact .ge l r s
  | seqSkip => exact .seqSkip
  | ifTrue => exact .ifTrue
  | ifFalse => exact .ifFalse
  | «while» => exact .while
  | appFun value => exact .appFun value
  | letValue value => exact .letValue value
  | letRecFun => exact .letRecFun
  | fstValue left right => exact .fstValue left right
  | sndValue left right => exact .sndValue left right
  | matchLeft value => exact .matchLeft value
  | matchRight value => exact .matchRight value
  | projectValue i ready => exact .projectValue i ready
  | refValue value fresh => exact .refValue value fresh
  | derefValue lookup => exact .derefValue lookup
  | assignValue value present => exact .assignValue value present

private theorem Step.toContextStepWith {assignmentLhs : Value → Prop} {before after : Config}
    (step : Step before after) (locations : ∀ loc : Loc, assignmentLhs ⟨.loc loc, .loc loc⟩) :
    ContextStepWith assignmentLhs before after := by
  induction step with
  | add l r s => exact .compute (.add l r s)
  | ge l r s => exact .compute (.ge l r s)
  | binaryLeft _ ih => exact .eval (.binaryLeft _ _) trivial ih
  | binaryRight value _ ih => exact .eval (.binaryRight ⟨_, value⟩ _) trivial ih
  | seqSkip => exact .compute .seqSkip
  | seqStep _ ih => exact .eval (.seq _) trivial ih
  | ifTrue => exact .compute .ifTrue
  | ifFalse => exact .compute .ifFalse
  | ifStep _ ih => exact .eval (.cond _ _) trivial ih
  | «while» => exact .compute .while
  | appLeft _ ih => exact .eval (.appLeft _) trivial ih
  | appRight value _ ih => exact .eval (.appRight ⟨_, value⟩) trivial ih
  | appFun value => exact .compute (.appFun value)
  | letStep _ ih => exact .eval (.letE _ _) trivial ih
  | letValue value => exact .compute (.letValue value)
  | letRecFun => exact .compute .letRecFun
  | pairLeft _ ih => exact .eval (.pairLeft _) trivial ih
  | pairRight value _ ih => exact .eval (.pairRight ⟨_, value⟩) trivial ih
  | fstValue left right => exact .compute (.fstValue left right)
  | sndValue left right => exact .compute (.sndValue left right)
  | fstStep _ ih => exact .eval .fst trivial ih
  | sndStep _ ih => exact .eval .snd trivial ih
  | inl _ ih => exact .eval (.inl _) trivial ih
  | inr _ ih => exact .eval (.inr _) trivial ih
  | matchStep _ ih => exact .eval (.matchSum _ _ _ _) trivial ih
  | matchLeft value => exact .compute (.matchLeft value)
  | matchRight value => exact .compute (.matchRight value)
  | @recordStep labels fields _ _ _ i earlier _ ih =>
      simpa only [EvalContext.plugConfig, EvalContext.plug, Function.update_eq_self] using
        ContextStepWith.eval (.recordField (labels := labels) fields i earlier) trivial ih
  | projectValue i ready => exact .compute (.projectValue i ready)
  | projectStep _ ih => exact .eval (.project _) trivial ih
  | refValue value fresh => exact .compute (.refValue value fresh)
  | refStep _ ih => exact .eval .ref trivial ih
  | derefValue lookup => exact .compute (.derefValue lookup)
  | derefStep _ ih => exact .eval .deref trivial ih
  | assignValue value present => exact .compute (.assignValue value present)
  | assignRight _ ih => exact .eval (.assignRight ⟨_, .loc _⟩) (locations _) ih
  | assignLeft _ ih => exact .eval (.assignLeft _) trivial ih

theorem Step.toContextStep {before after : Config} (step : Step before after) :
    ContextStep before after :=
  step.toContextStepWith (fun _ => trivial)

theorem Step.toLocationContextStep {before after : Config} (step : Step before after) :
    LocationContextStep before after :=
  step.toContextStepWith (fun loc => ⟨loc, rfl⟩)

/-- A frame respecting (assign2) lifts a direct step at its hole. -/
theorem EvalContext.liftStep (context : EvalContext) (allowed : context.Allows Value.IsLocation)
    {before after : Config} (inner : Step before after) :
    Step (context.plugConfig before) (context.plugConfig after) := by
  obtain ⟨e, s⟩ := before
  obtain ⟨e', s'⟩ := after
  cases context with
  | binaryLeft => exact .binaryLeft inner
  | binaryRight left _ => exact .binaryRight left.property inner
  | cond => exact .ifStep inner
  | seq => exact .seqStep inner
  | appLeft => exact .appLeft inner
  | appRight fn => exact .appRight fn.property inner
  | letE => exact .letStep inner
  | pairLeft => exact .pairLeft inner
  | pairRight left => exact .pairRight left.property inner
  | fst => exact .fstStep inner
  | snd => exact .sndStep inner
  | inl => exact .inl inner
  | inr => exact .inr inner
  | matchSum => exact .matchStep inner
  | recordField fields i earlier =>
      have ready : ∀ j, j < i → IsValue (Function.update fields i e j) := by
        intro j beforeHole
        have different : j ≠ i := by
          intro equal
          subst j
          exact Nat.lt_irrefl _ beforeHole
        simpa only [Function.update_of_ne different] using earlier j beforeHole
      have focused : Step ⟨Function.update fields i e i, s⟩ ⟨e', s'⟩ := by
        simpa only [Function.update_self] using inner
      simpa only [plugConfig, plug, Function.update_idem] using Step.recordStep i ready focused
  | project => exact .projectStep inner
  | assignLeft => exact .assignLeft inner
  | assignRight value =>
      obtain ⟨address, address_eq⟩ := allowed
      simpa only [plugConfig, plug, address_eq] using (Step.assignRight (loc := address) inner)
  | deref => exact .derefStep inner
  | ref => exact .refStep inner

theorem LocationContextStep.toStep {before after : Config} (step : LocationContextStep before after) :
    Step before after := by
  induction step with
  | compute compute => exact compute.toStep
  | eval context allowed _ ih => exact context.liftStep allowed ih

/-- The unrestricted form of Theorem 26 with the (assign2) location premise. -/
theorem locationContextStep_iff_step {before after : Config} :
    LocationContextStep before after ↔ Step before after :=
  ⟨LocationContextStep.toStep, Step.toLocationContextStep⟩

/-- Typing the expression in a frame types the expression at its hole in the
same variable environment. In particular, the frame never binds at the hole. -/
theorem EvalContext.hole_typed (context : EvalContext)
    {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ (context.plug e) T) : ∃ U, HasType Θ Γ e U := by
  cases context with
  | recordField _ i _ =>
      cases typed with
      | record fields =>
          exact ⟨_, by simpa only [Function.update_self] using fields i⟩
  | _ => cases typed <;> exact ⟨_, by assumption⟩

private theorem EvalContext.locationAssignment_of_typing (context : EvalContext)
    {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ (context.plug e) T) : context.Allows Value.IsLocation := by
  cases context with
  | assignRight value =>
      obtain ⟨lhs, ready⟩ := value
      cases typed with
      | assign lhsType _ =>
          cases ready <;> cases lhsType
          exact ⟨_, rfl⟩
  | _ => trivial

theorem ContextStep.toStep_of_hasType {before after : Config}
    {Θ : LocTypes} {Γ : VarTypes} {T : Ty}
    (step : ContextStep before after) (typed : HasType Θ Γ before.expr T) : Step before after := by
  induction step generalizing T with
  | compute compute => exact compute.toStep
  | eval context _ _ ih =>
      obtain ⟨_, hole⟩ := context.hole_typed typed
      exact context.liftStep (context.locationAssignment_of_typing typed) (ih hole)

/-- Theorem 26 for the contexts as printed, on sources having an L3 type.
The store is arbitrary. -/
theorem contextStep_iff_step_of_hasType {before after : Config}
    {Θ : LocTypes} {Γ : VarTypes} {T : Ty} (typed : HasType Θ Γ before.expr T) :
    ContextStep before after ↔ Step before after :=
  ⟨fun step => step.toStep_of_hasType typed, Step.toContextStep⟩

/-- An integer on the left of assignment distinguishes the two untyped relations. -/
theorem assignment_context_counterexample (s : Store) :
    let before : Config := ⟨.assign (.int 0) (.binary (.int 1) .add (.int 2)), s⟩
    let after : Config := ⟨.assign (.int 0) (.int 3), s⟩
    ContextStep before after ∧ Stuck before := by
  constructor
  · exact ContextStepWith.eval (assignmentLhs := fun _ => True)
      (.assignRight ⟨.int 0, .int 0⟩) trivial (.compute (.add 1 2 s))
  · constructor
    · intro value
      cases value
    · intro next step
      cases step with
      | assignLeft inner => cases inner

-- Allocation carries the store through both the pair and projection frames.
example (s : Store) (fresh : 0 ∉ s) :
    ContextStep ⟨.snd (.pair .skip (.ref (.int 7))), s⟩
      ⟨.snd (.pair .skip (.loc 0)), s.insert 0 ⟨.int 7, .int 7⟩⟩ :=
  .eval .snd trivial (.eval (.pairRight ⟨.skip, .skip⟩) trivial
    (.compute (.refValue ⟨.int 7, .int 7⟩ fresh)))

end Silmaril.Courses.Cambridge.L3
