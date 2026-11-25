module

public import Silmaril.Logic.Temporal.TLA.Rules.Figure5.Defs
public import Silmaril.Logic.Temporal.TLA.Thms

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.Rules.Figure5

open Silmaril.Logic.Temporal.TLA
open Formula

universe u

variable {S V W : Type u}

private theorem persists {p : Nat → Prop} {i : Nat} (initial : p i)
    (step : ∀ j, i ≤ j → p j → p (j + 1)) : ∀ j, i ≤ j → p j := by
  intro j hj
  have fromStart (n : Nat) : p (i + n) := by
    induction n with
    | zero => exact initial
    | succ n ih => exact step _ (Nat.le_add_right i n) ih
  exact Nat.add_sub_of_le hj ▸ fromStart (j - i)

theorem tla1 {P : StatePred S} {f : StateExpr S V}
    (preserveUnchanged : ∀ s t, P s → Action.unchanged f s t → P t)
    (σ : Behavior S) :
    (always (state P)).Sat σ ↔
      (conj (state P) (alwaysBracket (fun s t => P s → P t) f)).Sat σ := by
  constructor
  · intro h
    exact ⟨h 0 (Nat.le_refl 0), fun j _ => Or.inl fun _ => h (j + 1) (Nat.zero_le _)⟩
  · rintro ⟨initial, steps⟩
    apply persists initial
    intro j hj hp
    rcases steps j hj with preserve | unchanged
    · exact preserve hp
    · exact preserveUnchanged _ _ hp unchanged

theorem tla2 {P Q : StatePred S} {A B : Action S} {f : StateExpr S V} {g : StateExpr S W}
    (simulate : ∀ s t, P s → A.bracket f s t → Q s ∧ B.bracket g s t) :
    (conj (always (state P)) (alwaysBracket A f)).Entails
      (conj (always (state Q)) (alwaysBracket B g)) := by
  intro σ h
  have atStep j hj := simulate (σ j) (σ (j + 1)) (h.1 j hj) (h.2 j hj)
  exact ⟨fun j hj => (atStep j hj).1, fun j hj => (atStep j hj).2⟩

theorem inv2 {I : StatePred S} {N : Action S} {f : StateExpr S V}
    (σ : Behavior S) (invariant : (always (state I)).Sat σ) :
    (alwaysBracket N f).Sat σ ↔ (alwaysBracket (fun s t => N s t ∧ I s ∧ I t) f).Sat σ := by
  constructor
  · intro steps j hj
    rcases steps j hj with next | unchanged
    · exact Or.inl ⟨next, invariant j hj, invariant (j + 1) (Nat.zero_le _)⟩
    · exact Or.inr unchanged
  · intro steps j hj
    rcases steps j hj with next | unchanged
    · exact Or.inl next.1
    · exact Or.inr unchanged

private theorem leadsTo_of_fair_steps {P Q : StatePred S} {N A : Action S} {f : StateExpr S V}
    {σ : Behavior S} (steps : (alwaysBracket N f).Sat σ)
    (waiting : ∀ s t, P s → N.bracket f s t → P t ∨ Q t)
    (progress : ∀ s t, P s → Action.angle (fun x y => N x y ∧ A x y) f s t → Q t)
    (fairStep : ∀ i, (∀ j, i ≤ j → P (σ j)) →
      ∃ j, i ≤ j ∧ A.angle f (σ j) (σ (j + 1))) :
    ((state P).leadsTo (state Q)).Sat σ := by
  apply (holds_leadsTo _ _ σ 0).mpr
  intro i _ hp
  apply Classical.byContradiction
  intro noQ
  have after : ∀ j, i ≤ j → P (σ j) := persists (p := fun j => P (σ j)) hp fun j hj holdP =>
    (waiting _ _ holdP (steps j (Nat.zero_le j))).resolve_right
      (fun hq => noQ ⟨j + 1, Nat.le_succ_of_le hj, hq⟩)
  obtain ⟨j, hj, taken⟩ := fairStep i after
  have next := (steps j (Nat.zero_le j)).resolve_right taken.2
  exact noQ ⟨j + 1, Nat.le_succ_of_le hj, progress _ _ (after j hj) ⟨⟨next, taken.1⟩, taken.2⟩⟩

theorem wf1 {P Q : StatePred S} {N A : Action S} {f : StateExpr S V}
    (waiting : ∀ s t, P s → N.bracket f s t → P t ∨ Q t)
    (progress : ∀ s t, P s → Action.angle (fun x y => N x y ∧ A x y) f s t → Q t)
    (enabled : ∀ s, P s → (A.angle f).enabled s) :
    (conj (alwaysBracket N f) (weakFair A f)).Entails ((state P).leadsTo (state Q)) := by
  intro σ h
  apply leadsTo_of_fair_steps h.1 waiting progress
  intro i after
  exact (holds_weakFair A f σ 0).mp h.2
    ⟨i, Nat.zero_le i, fun j hj => enabled _ (after j hj)⟩ i (Nat.zero_le i)

theorem sf1 {P Q : StatePred S} {N A : Action S} {f : StateExpr S V} {F : Formula S}
    (waiting : ∀ s t, P s → N.bracket f s t → P t ∨ Q t)
    (progress : ∀ s t, P s → Action.angle (fun x y => N x y ∧ A x y) f s t → Q t)
    (enabled : (conj (always (state P)) (conj (alwaysBracket N f) (always F))).Entails
      (eventually (state (A.angle f).enabled))) :
    (conj (alwaysBracket N f) (conj (strongFair A f) (always F))).Entails
      ((state P).leadsTo (state Q)) := by
  intro σ h
  apply leadsTo_of_fair_steps h.1 waiting progress
  intro i after
  have recurrent : ∀ k, 0 ≤ k → ∃ j, k ≤ j ∧ (A.angle f).enabled (σ j) := by
    intro k _
    let m := max i k
    have onSuffix := enabled (σ.suffix m)
      ⟨((always (state P)).sat_suffix σ m).mpr (fun j hj => after j (Nat.le_trans (Nat.le_max_left ..) hj)),
       ((alwaysBracket N f).sat_suffix σ m).mpr (fun j _ => h.1 j (Nat.zero_le j)),
       ((always F).sat_suffix σ m).mpr (fun j _ => h.2.2 j (Nat.zero_le j))⟩
    have fromM := ((eventually (state (A.angle f).enabled)).sat_suffix σ m).mp onSuffix
    obtain ⟨j, hj, hjEnabled⟩ := (holds_eventually _ σ m).mp fromM
    exact ⟨j, Nat.le_trans (Nat.le_max_right ..) hj, hjEnabled⟩
  exact (holds_strongFair A f σ 0).mp h.2.1 recurrent i (Nat.zero_le i)

private theorem holds_weakFairWithEnabled (M : Action S) (g : StateExpr S W)
    (enabled : StatePred S) (σ : Behavior S) (i : Nat) :
    (weakFairWithEnabled M g enabled).Holds σ i ↔
      ((∃ j, i ≤ j ∧ ∀ k, j ≤ k → enabled (σ k)) →
        ∀ j, i ≤ j → ∃ k, j ≤ k ∧ M.angle g (σ k) (σ (k + 1))) := by
  classical
  simp only [weakFairWithEnabled, holds_disj, Holds, holds_eventuallyAngle, holds_eventually]
  rw [or_comm, Classical.or_iff_not_imp_left]
  simp only [Classical.not_forall, exists_prop, not_exists, Decidable.not_and_not_right]

private theorem holds_strongFairWithEnabled (M : Action S) (g : StateExpr S W)
    (enabled : StatePred S) (σ : Behavior S) (i : Nat) :
    (strongFairWithEnabled M g enabled).Holds σ i ↔
      ((∀ j, i ≤ j → ∃ k, j ≤ k ∧ enabled (σ k)) →
        ∀ j, i ≤ j → ∃ k, j ≤ k ∧ M.angle g (σ k) (σ (k + 1))) := by
  classical
  simp only [strongFairWithEnabled, holds_disj, Holds, holds_eventuallyAngle, holds_eventually]
  rw [or_comm, Classical.or_iff_not_imp_left]
  simp only [not_exists, not_and, Classical.not_forall, exists_prop, Classical.not_not]

/-- Past the last target angle step, every source step satisfies the bracket
with B removed. Apply the stabilization premise at that suffix. -/
private theorem stabilize_without_target {P : StatePred S} {N B M : Action S}
    {f : StateExpr S V} {g : StateExpr S W} {Fair F Enablement : Formula S}
    {σ : Behavior S} {i : Nat}
    (steps : (alwaysBracket N f).Sat σ)
    (simulate : ∀ s t, Action.angle (fun x y => N x y ∧ B x y) f s t → M.angle g s t)
    (stabilize : (conj (alwaysBracket (fun s t => N s t ∧ ¬ B s t) f)
      (conj Fair (conj (always F) Enablement))).Entails (eventually (always (state P))))
    (live : (conj Fair (conj (always F) Enablement)).Holds σ i)
    (noTarget : ∀ j, i ≤ j → ¬ M.angle g (σ j) (σ (j + 1))) :
    ∃ k, i ≤ k ∧ ∀ j, k ≤ j → P (σ j) := by
  have reduced : (alwaysBracket (fun s t => N s t ∧ ¬ B s t) f).Holds σ i := by
    intro j hj
    classical
    by_cases unchanged : Action.unchanged f (σ j) (σ (j + 1))
    · exact Or.inr unchanged
    · have next := (steps j (Nat.zero_le j)).resolve_right unchanged
      exact Or.inl ⟨next, fun b => noTarget j hj (simulate _ _ ⟨⟨next, b⟩, unchanged⟩)⟩
  have stable := stabilize (σ.suffix i) (((conj _ _).sat_suffix σ i).mpr ⟨reduced, live⟩)
  exact (holds_eventually _ σ i).mp (((eventually (always (state P))).sat_suffix σ i).mp stable)

theorem wf2 {P enabled : StatePred S} {N A B M : Action S}
    {f : StateExpr S V} {g : StateExpr S W} {F : Formula S}
    (simulate : ∀ s t, Action.angle (fun x y => N x y ∧ B x y) f s t → M.angle g s t)
    (progress : ∀ s t, P s → P t →
      Action.angle (fun x y => N x y ∧ A x y) f s t → enabled s → B s t)
    (enableSource : ∀ s, P s → enabled s → (A.angle f).enabled s)
    (stabilize : (conj (alwaysBracket (fun s t => N s t ∧ ¬ B s t) f)
      (conj (weakFair A f) (conj (always F) (eventually (always (state enabled)))))).Entails
      (eventually (always (state P)))) :
    (conj (alwaysBracket N f) (conj (weakFair A f) (always F))).Entails
      (weakFairWithEnabled M g enabled) := by
  intro σ h
  change (weakFairWithEnabled M g enabled).Holds σ 0
  apply (holds_weakFairWithEnabled M g enabled σ 0).mpr
  rintro ⟨e, _, enabledFrom⟩ i _
  apply Classical.byContradiction
  intro noStep
  have noTarget j hj : ¬ M.angle g (σ j) (σ (j + 1)) := fun step => noStep ⟨j, hj, step⟩
  have targetEnabled : (eventually (always (state enabled))).Holds σ i :=
    (holds_eventually _ σ i).mpr
      ⟨max e i, Nat.le_max_right .., fun j hj => enabledFrom j (Nat.le_trans (Nat.le_max_left ..) hj)⟩
  have fair := (holds_weakFair A f σ 0).mp h.2.1
  have fairFrom : (weakFair A f).Holds σ i := (holds_weakFair A f σ i).mpr
    (fun ⟨j, _, hj⟩ k _ => fair ⟨j, Nat.zero_le j, hj⟩ k (Nat.zero_le k))
  obtain ⟨k, hik, pFrom⟩ := stabilize_without_target h.1 simulate stabilize
    ⟨fairFrom, fun j _ => h.2.2 j (Nat.zero_le j), targetEnabled⟩ noTarget
  let m := max k e
  have pAfter {j} (hj : m ≤ j) := pFrom j (Nat.le_trans (Nat.le_max_left ..) hj)
  have enabledAfter {j} (hj : m ≤ j) := enabledFrom j (Nat.le_trans (Nat.le_max_right ..) hj)
  obtain ⟨j, hj, taken⟩ := fair
    ⟨m, Nat.zero_le m, fun j hj => enableSource _ (pAfter hj) (enabledAfter hj)⟩ m (Nat.zero_le m)
  have next := (h.1 j (Nat.zero_le j)).resolve_right taken.2
  have b := progress _ _ (pAfter hj) (pAfter (Nat.le_succ_of_le hj))
    ⟨⟨next, taken.1⟩, taken.2⟩ (enabledAfter hj)
  exact noTarget j (Nat.le_trans hik (Nat.le_trans (Nat.le_max_left ..) hj))
    (simulate _ _ ⟨⟨next, b⟩, taken.2⟩)

theorem sf2 {P enabled : StatePred S} {N A B M : Action S}
    {f : StateExpr S V} {g : StateExpr S W} {F : Formula S}
    (simulate : ∀ s t, Action.angle (fun x y => N x y ∧ B x y) f s t → M.angle g s t)
    (progress : ∀ s t, P s → P t →
      Action.angle (fun x y => N x y ∧ A x y) f s t → B s t)
    (enableSource : ∀ s, P s → enabled s → (A.angle f).enabled s)
    (stabilize : (conj (alwaysBracket (fun s t => N s t ∧ ¬ B s t) f)
      (conj (strongFair A f) (conj (always F) (always (eventually (state enabled)))))).Entails
      (eventually (always (state P)))) :
    (conj (alwaysBracket N f) (conj (strongFair A f) (always F))).Entails
      (strongFairWithEnabled M g enabled) := by
  intro σ h
  change (strongFairWithEnabled M g enabled).Holds σ 0
  apply (holds_strongFairWithEnabled M g enabled σ 0).mpr
  intro targetRecurrent i _
  apply Classical.byContradiction
  intro noStep
  have noTarget j hj : ¬ M.angle g (σ j) (σ (j + 1)) := fun step => noStep ⟨j, hj, step⟩
  have targetEnabled : (always (eventually (state enabled))).Holds σ i :=
    fun j _ => (holds_eventually _ σ j).mpr (targetRecurrent j (Nat.zero_le j))
  have fair := (holds_strongFair A f σ 0).mp h.2.1
  have fairFrom : (strongFair A f).Holds σ i := (holds_strongFair A f σ i).mpr (fun recurrent j _ =>
    fair (fun k _ => by
      obtain ⟨l, hl, enabledAt⟩ := recurrent (max i k) (Nat.le_max_left ..)
      exact ⟨l, Nat.le_trans (Nat.le_max_right ..) hl, enabledAt⟩) j (Nat.zero_le j))
  obtain ⟨k, hik, pFrom⟩ := stabilize_without_target h.1 simulate stabilize
    ⟨fairFrom, fun j _ => h.2.2 j (Nat.zero_le j), targetEnabled⟩ noTarget
  have recurrent : ∀ j, 0 ≤ j → ∃ l, j ≤ l ∧ (A.angle f).enabled (σ l) := by
    intro j _
    obtain ⟨l, hl, enabledAt⟩ := targetRecurrent (max k j) (Nat.zero_le _)
    exact ⟨l, Nat.le_trans (Nat.le_max_right ..) hl,
      enableSource _ (pFrom l (Nat.le_trans (Nat.le_max_left ..) hl)) enabledAt⟩
  obtain ⟨j, hj, taken⟩ := fair recurrent k (Nat.zero_le k)
  have next := (h.1 j (Nat.zero_le j)).resolve_right taken.2
  have b := progress _ _ (pFrom j hj) (pFrom (j + 1) (Nat.le_succ_of_le hj))
    ⟨⟨next, taken.1⟩, taken.2⟩
  exact noTarget j (Nat.le_trans hik hj) (simulate _ _ ⟨⟨next, b⟩, taken.2⟩)

end Silmaril.Proofs.Logic.Temporal.TLA.Rules.Figure5
