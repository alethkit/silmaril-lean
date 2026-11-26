module

public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Order.ConditionallyCompleteLattice.WithTop
public import Mathlib.Order.Hom.Basic

/-!
# Undefined behaviour and refinement

An explicit model independently records possible results and possible UB
reasons. Its product order compares both sets by inclusion. In the
catastrophic model any possible UB is the added top. Defined models compare
by result inclusion, so every model refines a catastrophic specification.
In both orders implementations go on the left of `≤`.

An empty defined result set is bottom. It expresses a lack of outcomes.
A defined error can be recorded by taking `Result` to be an `Except` type.
-/

@[expose] public section

namespace Silmaril.Relational.UB

/-- Possible results, together with the set of reasons for possible UB. -/
abbrev Explicit (Result Reason : Type*) := Set Result × Set Reason

/-- Defined results, or a fresh top standing for catastrophic UB. Even the
defined model admitting every result lies strictly below this top. -/
abbrev Catastrophic (Result : Type*) := WithTop (Set Result)

namespace Explicit

variable {Result Reason : Type*}

def results (sem : Explicit Result Reason) : Set Result := sem.1

def reasons (sem : Explicit Result Reason) : Set Reason := sem.2

/-- Record ordinary results and no UB. -/
def defined (results : Set Result) : Explicit Result Reason := (results, ∅)

/-- Record one UB reason and no ordinary results. -/
def undefined (reason : Reason) : Explicit Result Reason := (∅, {reason})

def Safe (sem : Explicit Result Reason) : Prop := sem.reasons = ∅

/-- Forget the UB reasons and retain the recorded results even at an unsafe input. -/
def forget (sem : Explicit Result Reason) : Set Result := sem.results

/-- Any possible UB takes precedence over both recorded results and UB reasons. -/
noncomputable def collapse (sem : Explicit Result Reason) : Catastrophic Result := by
  classical
  exact if sem.Safe then ↑sem.results else ⊤

end Explicit

namespace Catastrophic

variable {Result Reason : Type*}

def defined (results : Set Result) : Catastrophic Result := ↑results

/-- Erase the catastrophic tag. At UB every ordinary result is possible;
this may equal a defined model's ordinary results. -/
def forget : Catastrophic Result → Set Result
  | ⊤ => Set.univ
  | (results : Set Result) => results

/-- The greatest explicit representative: at UB it allows every result and
reason; at a defined model it allows only the listed results. -/
def reify : Catastrophic Result → Explicit Result Reason
  | ⊤ => ⊤
  | (results : Set Result) => Explicit.defined results

end Catastrophic

/-- Remove the empty behaviour. The inherited order excludes comparisons that
would use bottom as a witness. -/
abbrev WithoutBottom (A : Type*) [Bot A] := {sem : A // sem ≠ ⊥}

abbrev NonemptyExplicit (Result Reason : Type*) := WithoutBottom (Explicit Result Reason)

abbrev NonemptyCatastrophic (Result : Type*) := WithoutBottom (Catastrophic Result)

namespace WithoutBottom

variable {A : Type*}

/-- Include the nonbottom models and send the new bottom to the original empty model. -/
def restore [Bot A] : WithBot (WithoutBottom A) → A
  | ⊥ => ⊥
  | (sem : WithoutBottom A) => sem.val

/-- A join of nonbottom elements stays nonbottom. -/
instance [SemilatticeSup A] [OrderBot A] : SemilatticeSup (WithoutBottom A) where
  sup left right := ⟨left.val ⊔ right.val, fun h =>
    left.property (le_bot_iff.mp (le_sup_left.trans_eq h))⟩
  le_sup_left _ _ := le_sup_left (α := A)
  le_sup_right _ _ := le_sup_right (α := A)
  sup_le _ _ _ := sup_le (α := A)

/-- The top remains when it is distinct from bottom. -/
instance [PartialOrder A] [BoundedOrder A] [Nontrivial A] : OrderTop (WithoutBottom A) where
  top := ⟨⊤, top_ne_bot⟩
  le_top _ := le_top (α := A)

end WithoutBottom

end Silmaril.Relational.UB
