module

public import Silmaril.Semantics.Relational.UB.Defs
public import Mathlib.Order.GaloisConnection.Basic
import Silmaril.Proofs.Semantics.Relational.UB.Algebra

public section

namespace Silmaril.Relational.UB

variable {Result Reason : Type*}

namespace Explicit

theorem le_iff {impl spec : Explicit Result Reason} :
    impl ≤ spec ↔ impl.results ⊆ spec.results ∧ impl.reasons ⊆ spec.reasons := Iff.rfl

theorem forget_monotone : Monotone (forget (Result := Result) (Reason := Reason)) :=
  fun _ _ refine => refine.1

@[simp] theorem safe_defined (results : Set Result) : (defined (Reason := Reason) results).Safe :=
  rfl

@[simp] theorem forget_defined (results : Set Result) :
    (defined (Reason := Reason) results).forget = results := rfl

@[simp] theorem forget_undefined (reason : Reason) :
    (undefined (Result := Result) reason).forget = ∅ := rfl

theorem safe_of_le {impl spec : Explicit Result Reason} (refine : impl ≤ spec)
    (safe : spec.Safe) : impl.Safe :=
  le_bot_iff.mp (refine.2.trans_eq safe)

theorem defined_results_of_safe {sem : Explicit Result Reason} (safe : sem.Safe) :
    defined sem.results = sem :=
  Proofs.Relational.UB.defined_results_of_safe safe

theorem collapse_of_safe {sem : Explicit Result Reason} (safe : sem.Safe) :
    sem.collapse = Catastrophic.defined sem.results := by
  classical
  rw [collapse, ite_eq_left safe]
  rfl

theorem collapse_of_unsafe {sem : Explicit Result Reason} (notSafe : ¬ sem.Safe) :
    sem.collapse = ⊤ := by
  classical
  simp [collapse, notSafe]

@[simp] theorem collapse_defined (results : Set Result) :
    (defined (Reason := Reason) results).collapse = Catastrophic.defined results :=
  collapse_of_safe (safe_defined results)

@[simp] theorem collapse_undefined (reason : Reason) :
    (undefined (Result := Result) reason).collapse = ⊤ :=
  collapse_of_unsafe fun safe => (Set.singleton_nonempty reason).ne_empty safe

/-- Collapse is left adjoint to choosing the greatest explicit representative. -/
theorem collapse_le_iff (impl : Explicit Result Reason) (spec : Catastrophic Result) :
    impl.collapse ≤ spec ↔ impl ≤ spec.reify :=
  Proofs.Relational.UB.collapse_le_iff impl spec

theorem collapse_reify_gc :
    GaloisConnection (collapse (Result := Result) (Reason := Reason)) Catastrophic.reify :=
  collapse_le_iff

theorem collapse_monotone : Monotone (collapse (Result := Result) (Reason := Reason)) :=
  collapse_reify_gc.monotone_l

/-- Exact comparison after collapse. If the explicit specification admits UB,
collapse no longer checks inclusion of results or reasons. -/
theorem collapse_le_collapse_iff (impl spec : Explicit Result Reason) :
    impl.collapse ≤ spec.collapse ↔ ¬ spec.Safe ∨ impl ≤ spec :=
  Proofs.Relational.UB.collapse_le_collapse_iff impl spec

/-- Collapse identifies two different explicit models exactly when both admit UB. -/
theorem collapse_eq_collapse_iff (left right : Explicit Result Reason) :
    left.collapse = right.collapse ↔ left = right ∨ (¬ left.Safe ∧ ¬ right.Safe) :=
  Proofs.Relational.UB.collapse_eq_collapse_iff left right

theorem collapse_reflects_le_of_safe {impl spec : Explicit Result Reason} (safe : spec.Safe) :
    impl.collapse ≤ spec.collapse ↔ impl ≤ spec :=
  (collapse_le_collapse_iff impl spec).trans (or_iff_right (not_not_intro safe))

/-- The explicit round trip retains exactly the safe models and the largest
explicit model. -/
theorem reify_collapse_eq_iff (sem : Explicit Result Reason) :
    sem.collapse.reify = sem ↔ sem.Safe ∨ sem = ⊤ :=
  Proofs.Relational.UB.reify_collapse_eq_iff sem

/-- Both ways to discard UB agree exactly when the model is safe or already
records every ordinary result. -/
theorem collapse_forget_eq_iff (sem : Explicit Result Reason) :
    sem.collapse.forget = sem.forget ↔ sem.Safe ∨ sem.results = Set.univ :=
  Proofs.Relational.UB.collapse_forget_eq_iff sem

theorem ne_bot_iff (sem : Explicit Result Reason) :
    sem ≠ ⊥ ↔ sem.results.Nonempty ∨ sem.reasons.Nonempty :=
  Proofs.Relational.UB.explicit_ne_bot_iff sem

end Explicit

namespace Catastrophic

@[simp] theorem forget_defined (results : Set Result) : (defined results).forget = results := rfl

@[simp] theorem forget_top : (⊤ : Catastrophic Result).forget = Set.univ := rfl

theorem defined_le_defined {left right : Set Result} :
    defined left ≤ defined right ↔ left ⊆ right :=
  WithTop.coe_le_coe

/-- Ordinary result inclusion reflects the original comparison when it also
preserves the implication between catastrophic tags. -/
theorem le_iff {left right : Catastrophic Result} :
    left ≤ right ↔ left.forget ⊆ right.forget ∧ (left = ⊤ → right = ⊤) :=
  Proofs.Relational.UB.catastrophic_le_iff

theorem forget_monotone : Monotone (forget (Result := Result)) :=
  fun _ _ refine => (le_iff.mp refine).1

/-- Defined catastrophic models always round-trip. Realizing catastrophic UB
in an explicit model requires at least one reason. -/
theorem collapse_reify_eq_iff (sem : Catastrophic Result) :
    (reify (Reason := Reason) sem).collapse = sem ↔ sem ≠ ⊤ ∨ Nonempty Reason :=
  Proofs.Relational.UB.collapse_reify_eq_iff sem

theorem defined_ne_bot_iff (results : Set Result) :
    defined results ≠ ⊥ ↔ results.Nonempty :=
  Proofs.Relational.UB.catastrophic_defined_ne_bot_iff results

theorem no_common_lower_bound {a b : Result} (distinct : a ≠ b)
    (left right : NonemptyCatastrophic Result)
    (left_eq : left.val = defined {a}) (right_eq : right.val = defined {b}) :
    ¬ ∃ lower : NonemptyCatastrophic Result, lower ≤ left ∧ lower ≤ right :=
  Proofs.Relational.UB.catastrophic_no_common_lower_bound distinct left right left_eq right_eq

end Catastrophic

namespace WithoutBottom

variable {A : Type*}

/-- A pair admits a common lower bound after deleting bottom exactly when its
ambient meet survives. In that case the ambient meet is its greatest lower bound. -/
theorem common_lower_bound_iff [SemilatticeInf A] [OrderBot A] (left right : WithoutBottom A) :
    (∃ lower : WithoutBottom A, lower ≤ left ∧ lower ≤ right) ↔ left.val ⊓ right.val ≠ ⊥ :=
  ⟨fun ⟨lower, ll, lr⟩ h => lower.property (le_bot_iff.mp ((le_inf (α := A) ll lr).trans_eq h)),
    fun h => ⟨⟨_, h⟩, inf_le_left (α := A), inf_le_right (α := A)⟩⟩

/-- Adding a fresh bottom recovers the ambient order. In particular this gives
the complete lattice completion of both nonempty UB orders. -/
noncomputable def bottomCompletion [PartialOrder A] [OrderBot A] :
    WithBot (WithoutBottom A) ≃o A :=
  Proofs.Relational.UB.bottomCompletion

@[simp] theorem bottomCompletion_apply [PartialOrder A] [OrderBot A]
    (sem : WithBot (WithoutBottom A)) : bottomCompletion sem = restore sem :=
  Proofs.Relational.UB.bottomCompletion_apply sem

/-- The lattice on the bottom completion, transported along its order isomorphism. -/
@[instance_reducible] noncomputable def completionLattice [CompleteLattice A] :
    CompleteLattice (WithBot (WithoutBottom A)) :=
  (bottomCompletion (A := A)).completeLattice

end WithoutBottom

end Silmaril.Relational.UB
