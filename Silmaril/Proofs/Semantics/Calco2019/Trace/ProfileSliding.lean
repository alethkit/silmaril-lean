module

public import Silmaril.Semantics.Calco2019.Trace.ProfileSliding.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace.TwoBody
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

private theorem embed_nested {X C D U C' D' : K}
    {f : X ⟶ P.sum (P.sum C D) U} (hf : G.nested f) (c : C ⟶ C') (d : D ⟶ D') :
    G.nested (f ≫ P.map (P.map c d) (𝟙 U)) := by
  have e : P.map (P.map c d) (𝟙 U) ≫ P.assoc = P.assoc ≫ P.map c (P.map d (𝟙 U)) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.assoc, Coproducts.map]
    · simp [Coproducts.assoc, Coproducts.map]
  simpa only [Guardedness.nested, Category.assoc, e] using G.map hf c (P.map d (𝟙 U))

private theorem embed_external {X C D U C' D' : K}
    {f : X ⟶ P.sum (P.sum C D) U} (hf : G.guarded (f ≫ externalMark))
    (c : C ⟶ C') (d : D ⟶ D') :
    G.guarded ((f ≫ P.map (P.map c d) (𝟙 U)) ≫ externalMark) := by
  have e : P.map (P.map c d) (𝟙 U) ≫ externalMark = externalMark ≫ P.map (P.map c (𝟙 U)) d := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [externalMark, Coproducts.map]
    · simp [externalMark, Coproducts.map]
  simpa only [Category.assoc, e] using G.map hf (P.map c (𝟙 U)) d

private theorem follow_nested {X C D U V : K}
    {f : X ⟶ P.sum (P.sum C D) U} (hf : G.nested f) (k : U ⟶ P.sum (P.sum C D) V) :
    G.nested (f ≫ P.desc P.inl k) := by
  have e : P.desc P.inl k ≫ P.assoc = P.assoc ≫
      P.desc P.inl (P.desc (P.inl ≫ P.inr) (k ≫ P.assoc)) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.assoc]
    · simp [Coproducts.assoc]
  simpa only [Guardedness.nested, Category.assoc, e] using
    G.compose (P.desc (P.inl ≫ P.inr) (k ≫ P.assoc)) hf (by simpa using G.trivial (𝟙 C))

private theorem follow_external {X C D U V : K}
    {f : X ⟶ P.sum (P.sum C D) U} (hf : G.guarded (f ≫ externalMark))
    {k : U ⟶ P.sum (P.sum C D) V} (hk : G.nested k) :
    G.nested (f ≫ P.desc P.inl k) := by
  have e : P.desc P.inl k ≫ P.assoc = externalMark ≫
      P.desc (P.desc P.inl (k ≫ P.assoc)) (P.inl ≫ P.inr) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [externalMark, Coproducts.assoc, Coproducts.map]
    · simp [externalMark, Coproducts.assoc, Coproducts.map]
  simpa only [Guardedness.nested, Category.assoc, e] using
    G.compose (P.inl ≫ P.inr) hf (G.parallel (by simpa using G.trivial (𝟙 C)) hk)

private theorem nested_external {X C D U : K} {f : X ⟶ P.sum (P.sum C D) U}
    (hf : G.nested f) : G.guarded (f ≫ externalMark) := by
  have e : externalMark (C := C) (D := D) (U := U) ≫ P.assoc =
      P.assoc ≫ P.map (𝟙 C) P.swap := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [externalMark, Coproducts.map, Coproducts.assoc, Coproducts.swap]
    · simp [externalMark, Coproducts.map, Coproducts.assoc, Coproducts.swap]
  apply G.weaken
  simpa only [Guardedness.nested, Category.assoc, e] using G.map hf (𝟙 C) P.swap

variable {A B C D E F H J U V : K}
  (s : TwoBody P (P.sum A B) (P.sum E F) (P.sum C D) (P.sum H J) U V)

theorem marked_cuts_guard
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second))
    (hv : G.guarded ((P.inr ≫ s.second) ≫ externalMark)) :
    G.TraceGuard s.markedCutFirst ∧ G.TraceGuard s.markedCutSecond := by
  let r₁ : P.sum C D ⟶ P.sum (P.sum C H) (P.sum D J) := P.map P.inl P.inl
  let r₂ : P.sum H J ⟶ P.sum (P.sum C H) (P.sum D J) := P.map P.inr P.inr
  let a := P.inl ≫ P.inl ≫ s.first ≫ P.map r₁ (𝟙 V)
  let u := P.inr ≫ s.first ≫ P.map r₁ (𝟙 V)
  let e := P.inl ≫ P.inl ≫ s.second ≫ P.map r₂ (𝟙 U)
  let v := P.inr ≫ s.second ≫ P.map r₂ (𝟙 U)
  have hₐ : G.nested a := by simpa [a, r₁] using embed_nested ha P.inl P.inl
  have hᵤ : G.nested u := by simpa [u, r₁] using embed_nested hu P.inl P.inl
  have hₑ : G.nested e := by simpa [e, r₂] using embed_nested he P.inr P.inr
  have hᵥ : G.guarded (v ≫ externalMark) := by simpa [v, r₂] using embed_external hv P.inr P.inr
  constructor
  · apply (restore_guard_iff _).2
    constructor
    · unfold Guardedness.nested
      rw [show P.inl ≫ P.inl ≫ tighten s.cutFirst TwoBody.slideEntry TwoBody.slideExit =
          P.desc (a ≫ P.desc P.inl v) e by
        apply P.hom_ext <;> simp [tighten, TwoBody.cutFirst, TwoBody.slideEntry, TwoBody.slideExit,
          TwoBody.firstEntry, TwoBody.secondEntry, TwoBody.firstStep, TwoBody.secondStep,
          Coproducts.map, a, e, v, r₁, r₂]]
      simpa only [P.desc_comp] using G.parallel (follow_nested hₐ v) hₑ
    · simpa [tighten, TwoBody.cutFirst, TwoBody.firstStep, TwoBody.secondStep, TwoBody.slideExit,
        Coproducts.map, u, v, r₁, r₂] using follow_nested hᵤ v
  · apply (restore_guard_iff _).2
    constructor
    · unfold Guardedness.nested
      rw [show P.inl ≫ P.inl ≫ tighten s.cutSecond TwoBody.slideEntry TwoBody.slideExit =
          P.desc a (e ≫ P.desc P.inl u) by
        apply P.hom_ext <;> simp [tighten, TwoBody.cutSecond, TwoBody.slideEntry, TwoBody.slideExit,
          TwoBody.firstEntry, TwoBody.secondEntry, TwoBody.firstStep, TwoBody.secondStep,
          Coproducts.map, a, e, u, r₁, r₂]]
      simpa only [P.desc_comp] using G.parallel hₐ (follow_nested hₑ u)
    · simpa [tighten, TwoBody.cutSecond, TwoBody.firstStep, TwoBody.secondStep, TwoBody.slideExit,
        Coproducts.map, u, v, r₁, r₂] using follow_external hᵥ hᵤ

theorem marked_slide (T : G.Conway) (hu : G.nested (P.inr ≫ s.first))
    (hf : G.TraceGuard s.markedCutFirst) (hs : G.TraceGuard s.markedCutSecond) :
    T.toFixpoints.guardedTrace hf = T.toFixpoints.guardedTrace hs := by
  let g : G.guarded (P.inr ≫ s.first) ∨ G.guarded (P.inr ≫ s.second) := Or.inl (G.weaken hu)
  have h := cuts_guarded s g
  have slide := slideTwoBodies s g T h.1 h.2
  have left : T.toFixpoints.guardedTrace hf =
      TwoBody.slideEntry ≫ T.toFixpoints.feedback s.cutFirst h.1 ≫ TwoBody.slideExit :=
    (trace_eq (traceBody_restore _) _ (tighten_feedbackGuard _ _ _ h.1)).trans
      (feedback_tighten T _ _ _ h.1)
  have right : T.toFixpoints.guardedTrace hs =
      TwoBody.slideEntry ≫ T.toFixpoints.feedback s.cutSecond h.2 ≫ TwoBody.slideExit :=
    (trace_eq (traceBody_restore _) _ (tighten_feedbackGuard _ _ _ h.2)).trans
      (feedback_tighten T _ _ _ h.2)
  rw [left, right, slide]

theorem marked_cuts_guard_I {I : K} (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum E I) (P.sum C D) (P.sum H I) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second)) :
    G.TraceGuard s.markedCutFirst ∧ G.TraceGuard s.markedCutSecond := by
  apply marked_cuts_guard s ha hu he
  let forget : P.sum (P.sum H I) U ⟶ P.sum H U := P.desc (P.desc P.inl (i.to _)) P.inr
  have e : externalMark (C := H) (D := I) (U := U) = forget ≫ P.inl := by
    apply P.hom_ext
    · apply P.hom_ext
      · simp [externalMark, forget, Coproducts.map]
      · exact i.hom_ext _ _
    · simp [externalMark, forget]
  rw [e, ← Category.assoc]
  exact G.trivial ((P.inr ≫ s.second) ≫ forget)

theorem marked_cuts_guard_II {I : K} (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum I F) (P.sum C D) (P.sum I J) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (hv : G.guarded ((P.inr ≫ s.second) ≫ externalMark)) :
    G.TraceGuard s.markedCutFirst ∧ G.TraceGuard s.markedCutSecond := by
  refine marked_cuts_guard s ha hu ?_ hv
  unfold Guardedness.nested
  rw [show (P.inl ≫ P.inl ≫ s.second) ≫ P.assoc = i.to _ from i.hom_ext _ _]
  exact G.initial i

theorem marked_cuts_guard_III
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first))
    (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second))
    (hv : G.nested (P.inr ≫ s.second)) :
    G.TraceGuard s.markedCutFirst ∧ G.TraceGuard s.markedCutSecond :=
  marked_cuts_guard s ha hu he (nested_external hv)

end Silmaril.Calco2019.Proofs.Feedback
