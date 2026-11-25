module

import Silmaril.Logic.Temporal.TLA.General.Thms

/-! Kernel-checked scoped TLA examples with Bool flags and Nat clocks. -/

namespace Silmaril.Logic.Temporal.TLA.General.Examples

open Silmaril.Logic.Temporal.TLA (Behavior Retiming StutterEquiv)
open Silmaril.Logic.Temporal.TLA.General

private inductive Kind where
  | flag
  | clock

private def Carrier : Kind → Type
  | .flag => Bool
  | .clock => Nat

private def one : Scope Kind where
  rigid := fun _ => Empty
  flex
    | .flag => Unit
    | .clock => Empty

private def noParams : RigidEnv Carrier one := fun _ x => nomatch x

private def flagState (x : Bool) : State Carrier one
  | .flag, _ => x
  | .clock, v => nomatch v

private def visible : Behavior (State Carrier one)
  | 0 => flagState false
  | _ + 1 => flagState true

private def stagedValues (s : State Carrier (one.bindFlex .flag)) : Bool × Bool :=
  (s .flag (Context.old ()), s.last)

private def stage (s t : Bool × Bool) : Prop :=
  (s = (false, false) ∧ t = (false, true)) ∨
    (s = (false, true) ∧ t = (true, true))

private def body : Formula Carrier (one.bindFlex .flag) :=
  .conj (.state (.atom fun _ s => stagedValues s = (false, false)))
    (.alwaysBracket (fun _ s t => stage (stagedValues s) (stagedValues t)) (fun _ => stagedValues))

private def repeatInitial : Retiming where
  index i := i - 1
  zero := rfl
  step i := by cases i with
    | zero => exact Or.inl rfl
    | succ i => exact Or.inr rfl
  cofinal j := ⟨j + 1, Nat.le_refl j⟩

private def stagedRun : Behavior (State Carrier (one.bindFlex .flag)) :=
  fun i => (visible.retime repeatInitial i).extend (i != 0)

private theorem stagedRun_sat : body.Sat noParams stagedRun := by
  refine ⟨rfl, ?_⟩
  intro n _
  match n with
  | 0 => exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  | 1 => exact Or.inl (Or.inr ⟨rfl, rfl⟩)
  | _ + 2 => exact Or.inr rfl

private def withClock : Scope Kind := one.bindFlex .clock

private def widen : Scope.Rename one withClock :=
  ⟨Context.Rename.id _, fun _ x => Context.old x⟩

private theorem widen_inj : widen.flex.Injective := fun _ _ _ h => Sum.inl.inj h

private def ambient : Model Carrier withClock :=
  ⟨noParams, fun i => (visible i).extend i⟩

/-- The extra ambient clock advances immediately. Hiding still admits an
initial hidden step, by repeating the entire ambient state. An extended
behavior on the original ambient timeline cannot satisfy the translated body. -/
example : ((Formula.existsFlex .flag body).rename widen).Satisfies ambient ∧
    ¬ ∃ τ : Behavior (State Carrier (withClock.bindFlex .flag)),
      τ.map Valuation.drop = ambient.behavior ∧
        (body.rename (widen.underFlex .flag)).Sat noParams τ := by
  constructor
  · apply (Formula.satisfies_rename _ widen widen_inj ambient).mpr
    exact (Formula.sat_existsFlex body noParams visible).mpr
      ⟨stagedRun, StutterEquiv.retime visible repeatInitial, stagedRun_sat⟩
  · rintro ⟨τ, same, sat⟩
    have h := (Formula.sat_rename body (widen.underFlex .flag) (widen_inj.under .flag)
      noParams τ).mp sat
    let reduced := τ.map (Valuation.restrict (widen.underFlex .flag).flex)
    have init : stagedValues (reduced 0) = (false, false) := h.1
    have step : (TLA.Action.bracket stage id) (stagedValues (reduced 0))
        (stagedValues (reduced 1)) := h.2 0 (Nat.zero_le _)
    have high : (stagedValues (reduced 1)).1 = true :=
      congrArg (fun s : State Carrier withClock => s .flag (Context.old ())) (congrFun same 1)
    rw [init] at step
    change stage (false, false) (stagedValues (reduced 1)) ∨
      stagedValues (reduced 1) = (false, false) at step
    simp [stage] at step
    rcases step with step | step <;> simp [step] at high

private def sameRigid : Formula Carrier (one.bindRigid .flag) :=
  .always (.state (.atom fun ρ s => s .flag () = ρ.last))

private def sameFlex : Formula Carrier (one.bindFlex .flag) :=
  .always (.state (.atom fun _ s => (stagedValues s).1 = s.last))

/-- A flexible witness can follow a changing flag. One rigid value cannot
agree with both values of the same flag on the behavior. -/
example : (Formula.existsFlex .flag sameFlex).Sat noParams visible ∧
    ¬ (Formula.existsRigid .flag sameRigid).Sat noParams visible := by
  refine ⟨(Formula.sat_existsFlex _ _ _).mpr ?_, ?_⟩
  · refine ⟨fun i => (visible i).extend (visible i .flag ()), StutterEquiv.refl visible, ?_⟩
    intro n
    rfl
  · rintro ⟨v, h⟩
    have low : false = v := h 0
    have high : true = v := h 1
    exact Bool.noConfusion (low.trans high.symm)

private def distinguishes : Action Carrier (one.bindFlex .flag) :=
  fun _ _ t => (stagedValues t).1 ≠ t.last

private def identify : Scope.Rename (one.bindFlex .flag) one where
  rigid := Context.Rename.id _
  flex
    | .flag, _ => ()
    | .clock, .inl v => nomatch v
    | .clock, .inr ⟨h⟩ => nomatch h

/-- Identifying two flexible variables can lose an enabled successor.
The reduct of the source state exists, but the distinguishing target
valuation cannot lift through this renaming. -/
example : (StatePred.enabled distinguishes).eval noParams
    ((flagState false).restrict identify.flex) ∧
    ¬ ((StatePred.enabled distinguishes).rename identify).eval noParams (flagState false) := by
  refine ⟨⟨(flagState false).extend true, Bool.noConfusion⟩, ?_⟩
  rintro ⟨_, h⟩
  exact h rfl

/-- Weakening to an extra clock preserves enablement when the successor
sets the free Boolean flag. The current clock value can supply the new coordinate. -/
example : ((StatePred.enabled (fun _ _ t => t .flag () = true : Action Carrier one)).rename widen).eval
    noParams (ambient.behavior 0) := by
  apply (StatePred.eval_rename _ widen widen_inj _ _).mpr
  exact ⟨flagState true, rfl⟩

private def readClock (s : State Carrier withClock) : Nat :=
  s .clock (one.flex.fresh .clock)

private def tick : Formula Carrier withClock :=
  .alwaysBracket (fun _ s t => readClock t = readClock s + 1) (fun _ => readClock)

private def running (s : State Carrier withClock) : Bool := decide (0 < readClock s)

/-- A clock that increases by one or stutters refines a Boolean latch via
the computed observation that the clock has started. -/
example : Refines (tick.Sat noParams) running
    (TLA.Formula.alwaysBracket (fun s t => s = false ∧ t = true) id).Sat := by
  intro σ sat n hn
  have step : readClock (σ (n + 1)) = readClock (σ n) + 1 ∨
      readClock (σ (n + 1)) = readClock (σ n) := sat n hn
  change (running (σ n) = false ∧ running (σ (n + 1)) = true) ∨
    running (σ (n + 1)) = running (σ n)
  rcases step with next | same
  · by_cases zero : readClock (σ n) = 0
    · exact Or.inl (by simp [running, zero, next])
    · exact Or.inr (by simp [running, next, Nat.pos_of_ne_zero zero])
  · exact Or.inr (congrArg (fun k : Nat => decide (0 < k)) same)

end Silmaril.Logic.Temporal.TLA.General.Examples
