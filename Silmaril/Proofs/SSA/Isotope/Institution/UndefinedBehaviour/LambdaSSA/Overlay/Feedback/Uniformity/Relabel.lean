module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

universe v w x

variable {τ : Type v} {R S L : List τ} {α : Type w} {σ : Type x}
  (label : Fin R.length → Fin S.length)

private theorem map_internal (i : Fin R.length) :
    mapLabel label L (internal R L i) = internal S L (label i) := by
  change mapLabel label L (labelEquiv R L (.inl i)) = labelEquiv S L (.inl (label i))
  simp [mapLabel]

theorem mapLabel_type (m : LabelMap R S) (L : List τ) (i : Fin (R ++ L).length) :
    (S ++ L).get (mapLabel m.label L i) = (R ++ L).get i := by
  have eq := (labelEquiv R L).apply_symm_apply i
  cases side : (labelEquiv R L).symm i with
  | inl j =>
    rw [side] at eq
    subst i
    change (S ++ L).get (mapLabel m.label L (internal R L j)) = (R ++ L).get (internal R L j)
    rw [map_internal]
    change (S ++ L)[(m.label j).val] = (R ++ L)[j.val]
    rw [List.getElem_append_left (m.label j).isLt, List.getElem_append_left j.isLt]
    exact m.type_eq j
  | inr j =>
    rw [side] at eq
    subst i
    have mapped : mapLabel m.label L (labelEquiv R L (.inr j)) = labelEquiv S L (.inr j) := by
      simp [mapLabel]
    rw [mapped]
    change (S ++ L)[S.length + j.val] = (R ++ L)[R.length + j.val]
    simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

private theorem map_external (o : Outcome L.length α σ) :
    mapOutcome label (external R L o) = external S L o := by
  cases o with
  | ret i a s =>
    change Outcome.ret (mapLabel label L (labelEquiv R L (.inr i))) a s =
      Outcome.ret (labelEquiv S L (.inr i)) a s
    simp [mapLabel]
  | fault _ | diverge => rfl

private theorem split_outcome (o : Outcome (R ++ L).length α σ) :
    (∃ i a s, o = .ret (internal R L i) a s) ∨ ∃ t, o = external R L t := by
  cases o with
  | ret i a s =>
    cases e : (labelEquiv R L).symm i with
    | inl j =>
      have eq := (labelEquiv R L).apply_symm_apply i
      rw [e] at eq
      exact Or.inl ⟨j, a, s, congrArg (fun i => Outcome.ret i a s) eq.symm⟩
    | inr j =>
      have eq := (labelEquiv R L).apply_symm_apply i
      rw [e] at eq
      exact Or.inr ⟨.ret j a s, congrArg (fun i => Outcome.ret i a s) eq.symm⟩
  | fault s => exact Or.inr ⟨.fault s, rfl⟩
  | diverge => exact Or.inr ⟨.diverge, rfl⟩

private theorem internal_ne_external (i : Fin R.length) (a : Silmaril.Isotope.Value α)
    (s : σ) (o : Outcome L.length α σ) :
    Outcome.ret (internal R L i) a s ≠ external R L o := by
  intro eq
  cases o with
  | ret j b t =>
    have h : labelEquiv R L (.inl i) = labelEquiv R L (.inr j) := (Outcome.ret.inj eq).1
    cases (labelEquiv R L).injective h
  | fault _ | diverge => cases eq

private theorem external_injective (R L : List τ) :
    Function.Injective (external (α := α) (σ := σ) R L) := by
  intro a b eq
  cases a <;> cases b <;>
    simp only [external, Outcome.ret.injEq, Outcome.fault.injEq, reduceCtorEq] at eq ⊢
  case ret.ret i a s j b t =>
    exact ⟨Sum.inr.inj ((labelEquiv R L).injective eq.1), eq.2⟩
  case fault.fault => exact eq

private theorem mapped_top (b : Behaviour (R ++ L).length α σ) :
    b = ⊤ ↔ mapReturns label b = ⊤ := by
  cases b using WithTop.recTopCoe <;> simp [mapReturns]

private theorem mapped_ordinary (b : Behaviour (R ++ L).length α σ)
    (o : Outcome (S ++ L).length α σ) :
    (mapReturns label b).Ordinary o ↔ ∃ old, b.Ordinary old ∧ mapOutcome label old = o := by
  cases b using WithTop.recTopCoe
  · simp [mapReturns, Behaviour.Ordinary]
  · constructor
    · intro h
      obtain ⟨old, included, eq⟩ := h.2
      exact ⟨old, ⟨WithTop.coe_ne_top, included⟩, eq⟩
    · rintro ⟨old, included, eq⟩
      exact ⟨WithTop.coe_ne_top, old, included.2, eq⟩

theorem slide_bisimulation (body : Point S.length α σ → Behaviour (R ++ L).length α σ)
    (p : Point R.length α σ) :
    Bisimulation (fun a => body (a.map label)) (fun a => mapReturns label (body a)) (Point.map label) p := by
  constructor
  · intro a b _ edge
    cases edge with
    | @branch i value state ret =>
      exact .branch ((mapped_ordinary label _ _).mpr
        ⟨.ret (internal R L i) value state, ret, by simp only [mapOutcome, map_internal]⟩)
  · intro a b _ edge
    cases edge with
    | @branch i value state ret =>
      obtain ⟨old, included, eq⟩ := (mapped_ordinary label _ _).mp ret
      rcases split_outcome old with ⟨j, b, t, rfl⟩ | ⟨o, rfl⟩
      · simp only [mapOutcome, map_internal, Outcome.ret.injEq] at eq
        obtain ⟨labels, rfl, rfl⟩ := eq
        have moved : label j = i := Sum.inl.inj ((labelEquiv S L).injective labels)
        exact ⟨.block j b t, .branch included, by simp [Point.map, moved]⟩
      · exact (internal_ne_external i value state o ((map_external label o).symm.trans eq).symm).elim
  · intro a _
    exact mapped_top label (body (a.map label))
  · intro a _ o
    constructor
    · intro finish
      exact (mapped_ordinary label _ _).mpr
        ⟨external R L o, finish, map_external label o⟩
    · intro finish
      obtain ⟨old, included, eq⟩ := (mapped_ordinary label _ _).mp finish
      rcases split_outcome old with ⟨i, a, s, rfl⟩ | ⟨o', rfl⟩
      · exact (internal_ne_external (label i) a s o (by simpa only [mapOutcome, map_internal] using eq)).elim
      · rw [map_external] at eq
        obtain rfl := external_injective S L eq
        exact included

theorem relabel_bisimulation (e : Fin R.length ≃ Fin S.length) (f : Run R L α σ)
    (p : Point R.length α σ) : Bisimulation f (relabel e f) (Point.map e) p := by
  have unmap : (fun q : Point R.length α σ => f ((q.map e).map e.symm)) = f := by
    funext q
    cases q <;> simp [Point.map]
  have h := slide_bisimulation e (fun q => f (q.map e.symm)) p
  change Bisimulation _ (relabel e f) (Point.map e) p at h
  rwa [unmap] at h

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity
