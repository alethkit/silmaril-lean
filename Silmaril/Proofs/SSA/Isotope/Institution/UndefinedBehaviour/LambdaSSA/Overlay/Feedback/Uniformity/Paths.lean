module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe v w x

variable {τ : Type v} {R S L : List τ} {α : Type w} {σ : Type x}
  {f : Run R L α σ} {g : Run S L α σ} {p : Point R.length α σ} {q : Point S.length α σ}
  {map : Point R.length α σ → Point S.length α σ}

theorem close_eq_iff :
    close f p = close g q ↔
      (ReachesUB f p ↔ ReachesUB g q) ∧ (¬ ReachesUB f p → outcomes f p = outcomes g q) := by
  constructor
  · intro same
    have top := (close_eq_top_iff (f := f) (p := p)).symm.trans
      ((congrArg (· = ⊤) same).to_iff.trans close_eq_top_iff)
    exact ⟨top, fun safe => WithTop.coe_inj.mp
      ((close_of_noUB safe).symm.trans (same.trans (close_of_noUB fun h => safe (top.mpr h))))⟩
  · rintro ⟨top, ordinary⟩
    by_cases reached : ReachesUB f p
    · rw [close_eq_top_iff.mpr reached, close_eq_top_iff.mpr (top.mp reached)]
    · rw [close_of_noUB reached, close_of_noUB (fun h => reached (top.mpr h)), ordinary reached]

variable (h : Bisimulation f g map p)
include h

private theorem reaches_map {a : Point R.length α σ} (path : Reaches f p a) :
    Reaches g (map p) (map a) := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact ih.tail (h.forward path step)

private theorem reaches_lift (path : Reaches g (map p) q) :
    ∃ a, Reaches f p a ∧ map a = q := by
  induction path with
  | refl => exact ⟨p, .refl, rfl⟩
  | tail _ step ih =>
    obtain ⟨a, path, rfl⟩ := ih
    obtain ⟨b, lifted, eq⟩ := h.backward path step
    exact ⟨b, path.tail lifted, eq⟩

theorem reaches_iff : Reaches g (map p) q ↔ ∃ a, Reaches f p a ∧ map a = q :=
  ⟨reaches_lift h, fun ⟨_, path, eq⟩ => eq ▸ reaches_map h path⟩

theorem reachesUB_iff : ReachesUB f p ↔ ReachesUB g (map p) := by
  constructor
  · rintro ⟨a, path, top⟩
    exact ⟨map a, reaches_map h path, (h.top path).mp top⟩
  · rintro ⟨a, path, top⟩
    obtain ⟨b, lifted, rfl⟩ := reaches_lift h path
    exact ⟨b, lifted, (h.top lifted).mpr top⟩

theorem finite_iff (o : Outcome L.length α σ) : Feedback.Finite f p o ↔ Feedback.Finite g (map p) o := by
  constructor
  · rintro ⟨a, path, finish⟩
    exact ⟨map a, reaches_map h path, (h.outcome path o).mp finish⟩
  · rintro ⟨a, path, finish⟩
    obtain ⟨b, lifted, rfl⟩ := reaches_lift h path
    exact ⟨b, lifted, (h.outcome lifted o).mpr finish⟩

theorem infinite_iff : Infinite f p ↔ Infinite g (map p) := by
  constructor
  · rintro ⟨path, start, step⟩
    have reach (n : Nat) : Reaches f p (path n) := by
      induction n with
      | zero => rw [start]
      | succ n ih => exact ih.tail (step n)
    exact ⟨fun n => map (path n), congrArg map start, fun n => h.forward (reach n) (step n)⟩
  · rintro ⟨path, start, step⟩
    let Lift (n : Nat) := {a // Reaches f p a ∧ map a = path n}
    have next (n : Nat) (a : Lift n) : ∃ b, Step f a.val b ∧ map b = path (n + 1) :=
      h.backward a.property.1 (a.property.2.symm ▸ step n)
    let lifted : (n : Nat) → Lift n := Nat.rec ⟨p, .refl, start.symm⟩ fun n a =>
      ⟨(next n a).choose, a.property.1.tail (next n a).choose_spec.1, (next n a).choose_spec.2⟩
    exact ⟨fun n => (lifted n).val, rfl, fun n => (next n (lifted n)).choose_spec.1⟩

theorem close_eq : close f p = close g (map p) := by
  refine close_eq_iff.mpr ⟨reachesUB_iff h, fun _ => ?_⟩
  ext o
  exact or_congr (finite_iff h o) (and_congr_right fun _ => infinite_iff h)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity
