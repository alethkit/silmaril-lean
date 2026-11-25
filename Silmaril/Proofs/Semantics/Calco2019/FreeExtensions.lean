module

public import Silmaril.Semantics.Calco2019.FreeExtensions

public section

universe u v u' v'

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {O : Bimodule C D} {A : C} {B I V W : D}

theorem isFreeExtension_initial_iff (i : IsInitial I) (e : O.Hom A V) :
    O.IsFreeExtension e (i.to V) ↔ O.IsFreeObject e := by
  constructor
  · intro h X g
    obtain ⟨k, hk, hu⟩ := h X g (i.to X)
    exact ⟨k, hk.1, fun q hq => hu q ⟨hq, i.hom_ext _ _⟩⟩
  · intro h X g f
    obtain ⟨k, hk, hu⟩ := h X g
    exact ⟨k, ⟨hk, i.hom_ext _ _⟩, fun q hq => hu q hq.1⟩

theorem isFreeExtension_coprod_iff {d : O.Hom A W} (hd : O.IsFreeObject d)
    (l : W ⟶ V) (r : B ⟶ V) :
    O.IsFreeExtension (O.post d l) r ↔ Nonempty (IsColimit (BinaryCofan.mk l r)) := by
  classical
  constructor
  · intro h
    have med (X : D) (a : W ⟶ X) (b : B ⟶ X) :
        ∃! k : V ⟶ X, l ≫ k = a ∧ r ≫ k = b := by
      obtain ⟨k, hk, hu⟩ := h X (O.post d a) b
      have hl : l ≫ k = a :=
        (hd X (O.post d a)).unique ((O.post_comp d l k).trans hk.1) rfl
      refine ⟨k, ⟨hl, hk.2⟩, fun q hq => hu q ⟨?_, hq.2⟩⟩
      rw [← O.post_comp, hq.1]
    exact ⟨BinaryCofan.isColimitMk
      (fun s => (med _ s.inl s.inr).exists.choose)
      (fun s => (med _ s.inl s.inr).exists.choose_spec.1)
      (fun s => (med _ s.inl s.inr).exists.choose_spec.2)
      (fun s _ ha hb => (med _ s.inl s.inr).unique ⟨ha, hb⟩
        (med _ s.inl s.inr).exists.choose_spec)⟩
  · rintro ⟨colim⟩ X g h
    obtain ⟨a, ha, hau⟩ := hd X g
    refine ⟨colim.desc (BinaryCofan.mk a h), ⟨?_, colim.fac _ ⟨.right⟩⟩, ?_⟩
    · rw [← O.post_comp]
      exact (congrArg (O.post d) (colim.fac (BinaryCofan.mk a h) ⟨.left⟩)).trans ha
    · intro q hq
      apply colim.hom_ext
      rintro ⟨j⟩
      cases j with
      | left =>
        refine (hau (l ≫ q) ?_).trans (colim.fac (BinaryCofan.mk a h) ⟨.left⟩).symm
        exact (O.post_comp d l q).trans hq.1
      | right => exact hq.2.trans (colim.fac (BinaryCofan.mk a h) ⟨.right⟩).symm

end Silmaril.Calco2019.Proofs
