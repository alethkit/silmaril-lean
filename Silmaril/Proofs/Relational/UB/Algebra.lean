module

public import Silmaril.Relational.UB.Defs

public section

namespace Silmaril.Proofs.Relational.UB

open Silmaril.Relational.UB

variable {Result Reason : Type*}

theorem defined_results_of_safe {sem : Explicit Result Reason} (safe : sem.Safe) :
    Explicit.defined sem.results = sem :=
  Prod.ext rfl safe.symm

theorem collapse_le_iff (impl : Explicit Result Reason) (spec : Catastrophic Result) :
    impl.collapse ≤ spec ↔ impl ≤ spec.reify := by
  classical
  cases spec using WithTop.recTopCoe with
  | top => exact iff_of_true le_top le_top
  | coe results =>
    by_cases safe : impl.Safe
    · rw [Explicit.collapse, ite_eq_left safe]
      exact WithTop.coe_le_coe.trans
        ⟨fun subset => ⟨subset, safe.le⟩, fun refine => refine.1⟩
    · rw [Explicit.collapse, ite_eq_right safe]
      exact ⟨fun h => False.elim (WithTop.coe_ne_top (top_unique h)),
        fun h => False.elim (safe (le_bot_iff.mp h.2))⟩

theorem collapse_le_collapse_iff (impl spec : Explicit Result Reason) :
    impl.collapse ≤ spec.collapse ↔ ¬ spec.Safe ∨ impl ≤ spec := by
  classical
  by_cases safe : spec.Safe
  · have eq : spec.collapse = Catastrophic.defined spec.results := by
      simp [Explicit.collapse, safe, Catastrophic.defined]
    rw [eq, collapse_le_iff, or_iff_right (not_not_intro safe)]
    exact Iff.of_eq (congrArg (impl ≤ ·) (defined_results_of_safe safe))
  · have eq : spec.collapse = ⊤ := by simp [Explicit.collapse, safe]
    rw [eq]
    exact iff_of_true le_top (Or.inl safe)

theorem collapse_eq_collapse_iff (left right : Explicit Result Reason) :
    left.collapse = right.collapse ↔ left = right ∨ (¬ left.Safe ∧ ¬ right.Safe) := by
  classical
  constructor
  · intro eq
    by_cases leftSafe : left.Safe
    · have rightLe := ((collapse_le_collapse_iff right left).mp eq.ge).resolve_left
        (not_not_intro leftSafe)
      have rightSafe : right.Safe := le_bot_iff.mp (rightLe.2.trans_eq leftSafe)
      have leftLe := ((collapse_le_collapse_iff left right).mp eq.le).resolve_left
        (not_not_intro rightSafe)
      exact Or.inl (le_antisymm leftLe rightLe)
    · by_cases rightSafe : right.Safe
      · have leftLe := ((collapse_le_collapse_iff left right).mp eq.le).resolve_left
          (not_not_intro rightSafe)
        exact False.elim (leftSafe (le_bot_iff.mp (leftLe.2.trans_eq rightSafe)))
      · exact Or.inr ⟨leftSafe, rightSafe⟩
  · rintro (rfl | ⟨leftUB, rightUB⟩)
    · rfl
    · simp [Explicit.collapse, leftUB, rightUB]

theorem collapse_reify_eq_iff (spec : Catastrophic Result) :
    (Catastrophic.reify (Reason := Reason) spec).collapse = spec ↔
      spec ≠ ⊤ ∨ Nonempty Reason := by
  classical
  cases spec using WithTop.recTopCoe with
  | top =>
    change Explicit.collapse (⊤ : Explicit Result Reason) = ⊤ ↔ _ ∨ _
    have safeIff : (⊤ : Explicit Result Reason).Safe ↔ ¬ Nonempty Reason :=
      by
        change (Set.univ : Set Reason) = ∅ ↔ ¬ Nonempty Reason
        rw [Set.nonempty_iff_univ_nonempty, Set.nonempty_iff_ne_empty, not_not]
    simp [Explicit.collapse, safeIff]
  | coe results =>
    simp [Explicit.collapse, Catastrophic.reify, Explicit.defined, Explicit.Safe,
      Explicit.results, Explicit.reasons]

theorem reify_collapse_eq_iff (sem : Explicit Result Reason) :
    sem.collapse.reify = sem ↔ sem.Safe ∨ sem = ⊤ := by
  classical
  by_cases safe : sem.Safe
  · have eq : sem.collapse.reify = sem := by
      rw [Explicit.collapse, ite_eq_left safe]
      exact defined_results_of_safe safe
    exact iff_of_true eq (Or.inl safe)
  · simp [Explicit.collapse, Catastrophic.reify, safe, eq_comm]

theorem collapse_forget_eq_iff (sem : Explicit Result Reason) :
    sem.collapse.forget = sem.forget ↔ sem.Safe ∨ sem.results = Set.univ := by
  classical
  by_cases safe : sem.Safe
  · rw [Explicit.collapse, ite_eq_left safe]
    exact iff_of_true rfl (Or.inl safe)
  · rw [Explicit.collapse, ite_eq_right safe, or_iff_right safe]
    exact eq_comm

theorem catastrophic_le_iff {left right : Catastrophic Result} :
    left ≤ right ↔ left.forget ⊆ right.forget ∧ (left = ⊤ → right = ⊤) := by
  cases left using WithTop.recTopCoe <;> cases right using WithTop.recTopCoe
  · simp
  · simp
  · simp [Catastrophic.forget]
  · simp [Catastrophic.forget, WithTop.coe_le_coe]

theorem explicit_ne_bot_iff (sem : Explicit Result Reason) :
    sem ≠ ⊥ ↔ sem.results.Nonempty ∨ sem.reasons.Nonempty := by
  change sem ≠ (∅, ∅) ↔ _
  rw [Set.nonempty_iff_ne_empty, Set.nonempty_iff_ne_empty]
  simp only [ne_eq, Prod.ext_iff]
  exact not_and_or

theorem catastrophic_defined_ne_bot_iff (results : Set Result) :
    Catastrophic.defined results ≠ ⊥ ↔ results.Nonempty :=
  (not_congr WithTop.coe_eq_coe).trans Set.nonempty_iff_ne_empty.symm

section WithoutBottom

variable {A : Type*} [PartialOrder A] [OrderBot A]

noncomputable def insertBottom (sem : A) : WithBot (WithoutBottom A) := by
  classical
  exact if h : sem = ⊥ then ⊥ else (↑(⟨sem, h⟩ : WithoutBottom A))

noncomputable def bottomCompletion : WithBot (WithoutBottom A) ≃o A where
  toFun := WithoutBottom.restore
  invFun := insertBottom
  left_inv := by
    intro sem
    cases sem using WithBot.recBotCoe with
    | bot => simp [WithoutBottom.restore, insertBottom]
    | coe sem => simp [WithoutBottom.restore, insertBottom, sem.property]
  right_inv := by
    intro sem
    by_cases h : sem = ⊥
    · subst sem
      simp [insertBottom, WithoutBottom.restore]
    · simp [insertBottom, WithoutBottom.restore, h]
  map_rel_iff' := by
    intro left right
    cases left using WithBot.recBotCoe <;> cases right using WithBot.recBotCoe
    · simp [WithoutBottom.restore]
    · simp [WithoutBottom.restore]
    · rename_i sem
      simp [WithoutBottom.restore, le_bot_iff, sem.property]
    · exact (WithBot.coe_le_coe (α := WithoutBottom A)).symm

theorem bottomCompletion_apply (sem : WithBot (WithoutBottom A)) :
    bottomCompletion sem = WithoutBottom.restore sem := by
  change WithoutBottom.restore sem = WithoutBottom.restore sem
  exact Eq.refl _

end WithoutBottom

theorem catastrophic_no_common_lower_bound {a b : Result} (distinct : a ≠ b)
    (left right : NonemptyCatastrophic Result)
    (left_eq : left.val = Catastrophic.defined {a})
    (right_eq : right.val = Catastrophic.defined {b}) :
    ¬ ∃ lower : NonemptyCatastrophic Result, lower ≤ left ∧ lower ≤ right := by
  rintro ⟨lower, leLeft, leRight⟩
  have infEq : left.val ⊓ right.val = ⊥ := by
    rw [left_eq, right_eq]
    simp only [Catastrophic.defined, ← WithTop.coe_inf,
      (Set.disjoint_singleton.mpr distinct).eq_bot]
    rfl
  have below : lower.val ≤ left.val ⊓ right.val := le_inf leLeft leRight
  exact lower.property (le_bot_iff.mp (below.trans_eq infEq))

end Silmaril.Proofs.Relational.UB
