module

import Silmaril.Languages.Python.Core.Thms
meta import Silmaril.Languages.Python.Core.Thms
meta import Silmaril.Languages.Python.Core.Defs
meta import Silmaril.Semantics.Operational.Determinism.Fuel.Defs

open Silmaril.Languages.Python.Core Silmaril.Semantics.Operational

private def sum : Body := ⟨.binary .add (.int 2) (.int 5)⟩

example : Step sum.start none (.returning (.int 7)) :=
  .expr (.compute (.add 2 5))

example : (labelled .addition).Finishes sum.start [.ok 7] (.returned (.ok 7)) :=
  ⟨.finished (.ok 7), .silent ⟨rfl, .expr (.compute (.add 2 5))⟩
    (.visible ⟨rfl, .ret 7⟩ (.nil _)), rfl, .finished _⟩

example (outcome : Outcome Completion) :
    (model .addition).May sum outcome ↔ outcome = .returned (.ok 7) := by
  rw [model_may_iff]
  exact and_iff_right rfl

example : run .addition sum 0 = some (.exhausted sum.start) := rfl

example : run .addition sum 2 = some (.stop (.finished (.ok 7)) (.observed (.returned (.ok 7)))) := rfl

-- Both operands contain redexes. The left operand takes the first step.
private def nested : Body :=
  ⟨.binary .add (.binary .add (.int 18446744073709551615) (.int 1))
    (.binary .floorDiv (.int 7) (.int (-3)))⟩

example : nested.start.advance = some (none,
    .returning (.binary .add (.int 18446744073709551616) (.binary .floorDiv (.int 7) (.int (-3))))) :=
  rfl

example : run .arithmetic nested 4 =
    some (.stop (.finished (.ok 18446744073709551613))
      (.observed (.returned (.ok 18446744073709551613)))) := rfl

-- A failing left operand takes the exception path before the right redex.
private def divideByZero : Body :=
  ⟨.binary .add (.binary .floorDiv (.int 1) (.int 0))
    (.binary .add (.int 2) (.int 5))⟩

example : Step divideByZero.start none (.raising .zeroDivisionError) :=
  .expr (.left (.compute (.divZero 1)))

example : (labelled .arithmetic).Finishes divideByZero.start [.error .zeroDivisionError]
    (.returned (.error .zeroDivisionError)) :=
  (labelled_finishes_iff (body := divideByZero) rfl).mpr ⟨rfl, rfl⟩

example : run .arithmetic divideByZero 2 =
    some (.stop (.finished (.error .zeroDivisionError))
      (.observed (.returned (.error .zeroDivisionError)))) := rfl

example : ¬ (model .arithmetic).May divideByZero .trap := by
  rw [model_may_iff]
  simp

example : (model .addition).NoEntry divideByZero := noEntry_iff.mpr (by decide)

example : run .addition divideByZero 2 = none := rfl

example : ¬ (model .addition).UBReachable divideByZero := model_safe

example : (semantics .addition).UBReachable divideByZero.start :=
  ⟨_, .refl, .inr (by decide)⟩

example : (oracle .addition).run divideByZero.start 2 = .stop divideByZero.start .ub := rfl

#guard match run .addition sum 2 with
  | some (.stop _ (.observed (.returned (.ok result)))) => result == 7
  | _ => false

#print axioms State.advance_iff
#print axioms Step.deterministic
#print axioms progress
#print axioms noDiverges
#print axioms model_safe
#print axioms model_may_iff
#print axioms labelled_finishes_iff
#print axioms run_sound
#print axioms run_exact
