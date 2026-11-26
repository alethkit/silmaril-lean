module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe v w x

variable {τ : Type v} {R L : List τ} {α : Type w} {σ : Type x}
  {f g : Run R L α σ} {p : Point R.length α σ}

theorem close_eq_top_iff : close f p = ⊤ ↔ ReachesUB f p := by
  classical
  by_cases h : ReachesUB f p <;> simp [close, h]

theorem close_of_noUB (h : ¬ ReachesUB f p) : close f p = ↑(outcomes f p) := by
  classical
  simp [close, h]

theorem ordinary_close_iff {o : Outcome L.length α σ} :
    (close f p).Ordinary o ↔ ¬ ReachesUB f p ∧ o ∈ outcomes f p := by
  classical
  by_cases h : ReachesUB f p <;> simp [Behaviour.Ordinary, Behaviour.possible, close, h]

private theorem ordinary_mono {n : Nat} {b c : Behaviour n α σ} {o : Outcome n α σ}
    (bc : b ≤ c) (safe : c ≠ ⊤) (ho : b.Ordinary o) : c.Ordinary o := by
  cases c using WithTop.recTopCoe
  · exact (safe rfl).elim
  cases b using WithTop.recTopCoe
  · exact (ho.1 rfl).elim
  · exact ⟨safe, WithTop.coe_le_coe.mp bc ho.2⟩

private theorem step_mono {q r : Point R.length α σ} (le : f q ≤ g q)
    (safe : g q ≠ ⊤) (step : Step f q r) : Step g q r := by
  cases step with
  | branch ho => exact .branch (ordinary_mono le safe ho)

private theorem reaches_mono {q : Point R.length α σ} (le : ∀ a, f a ≤ g a)
    (safe : ¬ ReachesUB g p) (path : Reaches f p q) : Reaches g p q := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih =>
    exact ih.tail (step_mono (le _) (fun top => safe ⟨_, ih, top⟩) edge)

theorem close_mono (le : ∀ q, f q ≤ g q) : close f p ≤ close g p := by
  classical
  by_cases upper : ReachesUB g p
  · rw [close_eq_top_iff.mpr upper]
    exact le_top
  have safe : ∀ q, Reaches f p q → g q ≠ ⊤ :=
    fun q path top => upper ⟨q, reaches_mono le upper path, top⟩
  have lower : ¬ ReachesUB f p := by
    rintro ⟨q, path, top⟩
    exact safe q path (top_le_iff.mp (top ▸ le q))
  rw [close_of_noUB lower, close_of_noUB upper]
  apply WithTop.coe_le_coe.mpr
  intro o ho
  rcases ho with ⟨q, path, finish⟩ | ⟨rfl, path, start, steps⟩
  · exact Or.inl ⟨q, reaches_mono le upper path, ordinary_mono (le q) (safe q path) finish⟩
  · have reaches (i : Nat) : Reaches f p (path i) := by
      induction i with
      | zero => rw [start]
      | succ i ih => exact ih.tail (steps i)
    exact Or.inr ⟨rfl, path, start, fun i =>
      step_mono (le (path i)) (safe (path i) (reaches i)) (steps i)⟩

theorem infinite_unfold (h : Infinite f p) : ∃ q, Step f p q ∧ Infinite f q := by
  obtain ⟨path, start, steps⟩ := h
  exact ⟨path 1, start ▸ steps 0, fun j => path (j + 1), rfl, fun j => steps (j + 1)⟩

theorem close_top_unfold :
    close f p = ⊤ ↔ f p = ⊤ ∨ ∃ q, Step f p q ∧ close f q = ⊤ := by
  simp only [close_eq_top_iff]
  constructor
  · rintro ⟨q, path, top⟩
    rcases path.cases_head with rfl | ⟨t, edge, rest⟩
    · exact Or.inl top
    · exact Or.inr ⟨t, edge, q, rest, top⟩
  · rintro (top | ⟨q, edge, t, rest, top⟩)
    · exact ⟨p, .refl, top⟩
    · exact ⟨t, rest.head edge, top⟩

private theorem prepend_infinite {q : Point R.length α σ}
    (edge : Step f p q) (rest : Infinite f q) : Infinite f p := by
  obtain ⟨path, start, steps⟩ := rest
  let pathFromStart : Nat → Point R.length α σ
    | 0 => p
    | j + 1 => path j
  refine ⟨pathFromStart, rfl, ?_⟩
  intro j
  cases j with
  | zero =>
    change Step f p (path 0)
    exact start.symm ▸ edge
  | succ j => exact steps j

private theorem outcomes_unfold {o : Outcome L.length α σ} :
    o ∈ outcomes f p ↔ (f p).Ordinary (external R L o) ∨
      ∃ q, Step f p q ∧ o ∈ outcomes f q := by
  constructor
  · rintro (⟨q, path, finish⟩ | ⟨rfl, infinite⟩)
    · rcases path.cases_head with rfl | ⟨t, edge, rest⟩
      · exact Or.inl finish
      · exact Or.inr ⟨t, edge, Or.inl ⟨q, rest, finish⟩⟩
    · obtain ⟨t, edge, rest⟩ := infinite_unfold infinite
      exact Or.inr ⟨t, edge, Or.inr ⟨rfl, rest⟩⟩
  · rintro (finish | ⟨q, edge, ⟨t, path, finish⟩ | ⟨rfl, infinite⟩⟩)
    · exact Or.inl ⟨p, .refl, finish⟩
    · exact Or.inl ⟨t, path.head edge, finish⟩
    · exact Or.inr ⟨rfl, prepend_infinite edge infinite⟩

theorem close_ordinary_unfold {o : Outcome L.length α σ} (safe : close f p ≠ ⊤) :
    (close f p).Ordinary o ↔ (f p).Ordinary (external R L o) ∨
      ∃ q, Step f p q ∧ (close f q).Ordinary o := by
  have noUB : ¬ ReachesUB f p := fun top => safe (close_eq_top_iff.mpr top)
  rw [ordinary_close_iff, and_iff_right noUB, outcomes_unfold]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨q, edge, out⟩
    exact ⟨q, edge, ordinary_close_iff.mpr
      ⟨fun top => safe (close_top_unfold.mpr (Or.inr ⟨q, edge, close_eq_top_iff.mpr top⟩)), out⟩⟩
  · rintro ⟨q, edge, out⟩
    exact ⟨q, edge, (ordinary_close_iff.mp out).2⟩

private theorem infinite_of_serial (live : Point R.length α σ → Prop)
    (next : ∀ q, live q → ∃ t, Step f q t ∧ live t) (hp : live p) : Infinite f p := by
  let advance (q : {q // live q}) : {q // live q} :=
    ⟨(next q.val q.property).choose, (next q.val q.property).choose_spec.2⟩
  let path (n : Nat) : {q // live q} := Nat.rec ⟨p, hp⟩ (fun _ q => advance q) n
  exact ⟨fun j => (path j).val, rfl, fun j => (next (path j).val (path j).property).choose_spec.1⟩

/-- A coinductive witness can either reach local divergence or continue
forever through ordinary internal transfers. -/
theorem diverge_of_unfold (live : Point R.length α σ → Prop)
    (unfold : ∀ q, live q → (f q).Ordinary .diverge ∨ ∃ t, Step f q t ∧ live t)
    (hp : live p) : Finite f p .diverge ∨ Infinite f p := by
  classical
  by_cases terminal : Finite f p .diverge
  · exact Or.inl terminal
  · apply Or.inr
    apply infinite_of_serial (fun q => Reaches f p q ∧ live q) _ ⟨.refl, hp⟩
    intro q hq
    rcases unfold q hq.2 with finish | ⟨t, step, ht⟩
    · exact (terminal ⟨q, hq.1, finish⟩).elim
    · exact ⟨t, step, hq.1.tail step, ht⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback
