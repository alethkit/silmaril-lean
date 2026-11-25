module

public import Silmaril.Logic.Temporal.TLA.Defs

/-! The barred fairness formulas of Lamport §8.3.3 with explicit enabledness.
Strong fairness follows equation (18), as used in the SF2 premises of Fig. 5. -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Formula

universe u

variable {S V : Type u}

/-- The action and observation describe steps in the source space. The enabledness
predicate can be evaluated in a separate target space and pulled back. -/
def weakFairWithEnabled (A : Action S) (f : StateExpr S V) (enabled : StatePred S) :
    Formula S :=
  disj (.always (eventuallyAngle A f)) (.always (eventually (.state fun s => ¬ enabled s)))

/-- Recurrent angle steps or eventual continuous disabledness, with enabledness
supplied as a state predicate. -/
def strongFairWithEnabled (A : Action S) (f : StateExpr S V) (enabled : StatePred S) :
    Formula S :=
  disj (.always (eventuallyAngle A f)) (eventually (.always (.state fun s => ¬ enabled s)))

end Silmaril.Logic.Temporal.TLA.Formula
