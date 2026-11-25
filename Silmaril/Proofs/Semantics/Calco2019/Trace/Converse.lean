module

public import Silmaril.Semantics.Calco2019.Trace.Converse.Defs

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {trace : G.Feedback} (laws : Feedback.LocalLaws trace)

theorem trace_eq {A B U : K} {f g : P.sum A U ⟶ P.sum B U} (e : f = g)
    (hf : G.FeedbackGuard f) (hg : G.FeedbackGuard g) : trace f hf = trace g hg := by
  subst g
  rfl

private theorem map_id_id (B U : K) : P.map (𝟙 B) (𝟙 U) = 𝟙 (P.sum B U) := by
  simp [Coproducts.map]

private theorem onBranches_entry {A A' B U : K} (ht : Feedback.Tightening trace) (a : A' ⟶ A)
    (entry : A ⟶ P.sum B U) (body : U ⟶ P.sum B U) (hb : G.guarded body) :
    Feedback.onBranches trace (a ≫ entry) body hb =
      a ≫ Feedback.onBranches trace entry body hb := by
  let f := P.desc entry body
  have hf : G.FeedbackGuard f := by simpa [FeedbackGuard, f] using hb
  have e : tighten f a (𝟙 B) = P.desc (a ≫ entry) body := by
    simp [tighten, f, P.map_desc, map_id_id]
  exact (trace_eq e.symm _ (tighten_feedbackGuard f a (𝟙 B) hf)).trans (by simpa [f, Feedback.onBranches] using ht f a (𝟙 B) hf)

include laws in
theorem onBranches_result {A B B' U : K} (b : B ⟶ B')
    (entry : A ⟶ P.sum B U) (body : U ⟶ P.sum B U) (hb : G.guarded body) :
    Feedback.onBranches trace (entry ≫ P.map b (𝟙 U))
        (body ≫ P.map b (𝟙 U)) (G.map hb b (𝟙 U)) =
      Feedback.onBranches trace entry body hb ≫ b := by
  let f := P.desc entry body
  have hf : G.FeedbackGuard f := by simpa [FeedbackGuard, f] using hb
  have e : tighten f (𝟙 A) b = P.desc (entry ≫ P.map b (𝟙 U)) (body ≫ P.map b (𝟙 U)) := by
    simp [tighten, f, map_id_id]
  exact (trace_eq e.symm _ (tighten_feedbackGuard f (𝟙 A) b hf)).trans (by simpa [f, Feedback.onBranches] using laws.tighten f (𝟙 A) b hf)

private theorem onBranches_immediate {I B U : K} (i : IsInitial I)
    (ht : Feedback.Tightening trace) (hs : Feedback.Superposition trace) (body : U ⟶ P.sum B U)
    (hb : G.guarded body) :
    Feedback.onBranches trace (P.inl : B ⟶ P.sum B U) body hb = 𝟙 B := by
  let f := P.desc (i.to (P.sum B U)) body
  have hf : G.FeedbackGuard f := by simpa [FeedbackGuard, f] using hb
  let g := superpose f (𝟙 B)
  have hg : G.FeedbackGuard g := superpose_feedbackGuard f (𝟙 B) hf
  let fold : P.sum B B ⟶ B := P.desc (𝟙 B) (𝟙 B)
  have e : tighten g (P.inr : B ⟶ P.sum I B) fold = P.desc P.inl body := by
    apply P.hom_ext
    · simp [tighten, g, superpose, f, fold, Coproducts.map]
    · simp [tighten, g, superpose, f, fold, Coproducts.map]
  refine (trace_eq e.symm _ (tighten_feedbackGuard g P.inr fold hg)).trans ?_
  refine (ht g P.inr fold hg).trans ?_
  have eq : trace g hg = P.map (trace f hf) (𝟙 B) := hs f (𝟙 B) hf
  change P.inr ≫ trace g hg ≫ fold = 𝟙 B
  rw [eq]
  simp [Coproducts.map, fold]

include laws in
private theorem onBranches_enterState {B U : K} (body : U ⟶ P.sum B U) (hb : G.guarded body) :
    Feedback.onBranches trace (P.inr : U ⟶ P.sum B U) body hb =
      Feedback.iterate trace body hb := by
  let f := P.desc (P.inr : U ⟶ P.sum B U) P.inr
  have guard : G.guarded (P.inr ≫ f) ∨ G.guarded body := Or.inr hb
  have e : slideAfter f body = P.desc body body := by
    simp [slideAfter, f]
  have d : slideBefore f body = P.desc P.inr body := by
    simp [slideBefore, f]
  exact (trace_eq d.symm _ _).trans
    ((laws.slide f body guard).symm.trans (trace_eq e _ _))

theorem onBranches_formula_ofRouting {I A B U : K} (i : IsInitial I)
    (ht : Feedback.Tightening trace) (hs : Feedback.Superposition trace)
    (enter : ∀ {B U : K} (body : U ⟶ P.sum B U) (hb : G.guarded body),
      Feedback.onBranches trace P.inr body hb = Feedback.iterate trace body hb)
    (entry : A ⟶ P.sum B U)
    (body : U ⟶ P.sum B U) (hb : G.guarded body) :
    Feedback.onBranches trace entry body hb =
      entry ≫ P.desc (𝟙 B) (Feedback.iterate trace body hb) := by
  let f := Feedback.onBranches trace (𝟙 (P.sum B U)) body hb
  have e : Feedback.onBranches trace entry body hb = entry ≫ f := by
    simpa [f] using onBranches_entry ht entry (𝟙 (P.sum B U)) body hb
  refine e.trans (congrArg (entry ≫ ·) ?_)
  apply P.hom_ext
  · have a := onBranches_entry ht (P.inl : B ⟶ P.sum B U) (𝟙 (P.sum B U)) body hb
    rw [P.inl_desc]
    exact (by simpa [f] using a.symm :
      P.inl ≫ f = Feedback.onBranches trace P.inl body hb).trans
        (onBranches_immediate i ht hs body hb)
  · have a := onBranches_entry ht (P.inr : U ⟶ P.sum B U) (𝟙 (P.sum B U)) body hb
    rw [P.inr_desc]
    exact (by simpa [f] using a.symm :
      P.inr ≫ f = Feedback.onBranches trace P.inr body hb).trans (enter body hb)

include laws

theorem onBranches_formula [HasInitial K] {A B U : K} (entry : A ⟶ P.sum B U)
    (body : U ⟶ P.sum B U) (hb : G.guarded body) :
    Feedback.onBranches trace entry body hb = entry ≫ P.desc (𝟙 B) (Feedback.iterate trace body hb) :=
  onBranches_formula_ofRouting initialIsInitial laws.tighten laws.superpose
    (onBranches_enterState laws) entry body hb

theorem feedback_fixpoint [HasInitial K] {U B : K} (f : U ⟶ P.sum B U) (hf : G.guarded f) :
    IsFixpoint f (Feedback.iterate trace f hf) :=
  (onBranches_formula laws f f hf).symm

theorem feedback_naturality {U B B' : K} (f : U ⟶ P.sum B U) (b : B ⟶ B') (hf : G.guarded f)
    (hg : G.guarded (f ≫ P.map b (𝟙 U))) :
    Feedback.iterate trace (f ≫ P.map b (𝟙 U)) hg = Feedback.iterate trace f hf ≫ b :=
  onBranches_result laws b f f hf

theorem feedback_dinaturality [HasInitial K] {U V B : K} (g : U ⟶ P.sum B V)
    (h : V ⟶ P.sum B U) (guard : G.guarded g ∨ G.guarded h) :
    let body := G.dinaturality_bodies g h guard
    Feedback.iterate trace (g ≫ P.desc P.inl h) body.1 =
      g ≫ P.desc (𝟙 B) (Feedback.iterate trace (h ≫ P.desc P.inl g) body.2) := by
  let f := P.desc g g
  let bodies := G.dinaturality_bodies g h guard
  have guard' : G.guarded (P.inr ≫ f) ∨ G.guarded h := by simpa [f] using guard
  have e : slideAfter f h = P.desc (g ≫ P.desc P.inl h) (g ≫ P.desc P.inl h) := by simp [f, slideAfter]
  have d : slideBefore f h = P.desc g (h ≫ P.desc P.inl g) := by simp [f, slideBefore]
  exact ((trace_eq e.symm _ _).trans ((laws.slide f h guard').trans (trace_eq d _ _))).trans
    (onBranches_formula laws g _ bodies.2)

end Silmaril.Calco2019.Proofs.Feedback
