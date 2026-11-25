module

public import Silmaril.Semantics.Calco2019.Trace.ProfileLaws.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {I : K} (i : IsInitial I) (T : G.FourInterfaceTrace) (laws : T.LocalLaws)

include laws in
theorem reduced_superpose {A B U A' B' : K}
    (f : P.sum A U ⟶ P.sum B U) (g : A' ⟶ B') (hf : G.FeedbackGuard f) :
    T.toFeedback i (superpose f g) (superpose_feedbackGuard f g hf) =
      P.map (T.toFeedback i f hf) g := by
  let body := FourInterfaceTrace.feedbackBody i f
  let g' : P.sum I A' ⟶ P.sum B' I := P.desc (i.to A') (𝟙 A') ≫ g ≫ P.inl
  have hbody : G.TraceGuard body := FourInterfaceTrace.feedbackBody_guard i f hf
  have hg : G.guarded (P.inl ≫ g') := by
    rw [show P.inl ≫ g' = i.to _ from i.hom_ext _ _]
    exact G.initial i
  let hsp := traceSuperpose_guard hbody hg
  let a : P.sum A A' ⟶ P.sum (P.sum I I) (P.sum A A') := P.inr
  let b : P.sum (P.sum B B') (P.sum I I) ⟶ P.sum B B' :=
    P.desc (𝟙 _) (P.desc (i.to _) (i.to _))
  have m : tighten (traceBody (traceSuperpose body g')) a b = superpose f g := by
    rw [traceSuperpose, traceBody_restore]
    unfold body FourInterfaceTrace.feedbackBody
    rw [traceBody_restore]
    apply P.hom_ext
    · apply P.hom_ext <;> simp [tighten, superpose, exchangeMiddle, Coproducts.map, a, b, g']
    · simp [tighten, superpose, exchangeMiddle, Coproducts.map, a, b, g']
  have eq := T.toFeedback_tighten i laws.tighten _ a b (traceBody_guard hsp)
  refine (trace_eq m _ _).symm.trans (eq.trans ?_)
  rw [T.toFeedback_run i laws.tighten hsp, laws.superpose hbody hg]
  apply P.hom_ext <;> simp [a, b, g', exchangeMiddle, Coproducts.map, FourInterfaceTrace.toFeedback]

include laws in
private theorem reduce_profile_eq {A B C D U V A' B' : K}
    {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    {g : P.sum (P.sum A V) B ⟶ P.sum C (P.sum D V)}
    (hf : G.TraceGuard f) (hg : G.TraceGuard g) (h : T.run hf = T.run hg)
    (a : A' ⟶ P.sum A B) (b : P.sum C D ⟶ B')
    {m : P.sum A' U ⟶ P.sum B' U} {n : P.sum A' V ⟶ P.sum B' V}
    (em : tighten (traceBody f) a b = m) (en : tighten (traceBody g) a b = n)
    (hm : G.FeedbackGuard m) (hn : G.FeedbackGuard n) :
    T.toFeedback i m hm = T.toFeedback i n hn := by
  have q₁ := T.toFeedback_tighten i laws.tighten _ a b (traceBody_guard hf)
  have q₂ := T.toFeedback_tighten i laws.tighten _ a b (traceBody_guard hg)
  rw [T.toFeedback_run i laws.tighten hf, h] at q₁
  rw [T.toFeedback_run i laws.tighten hg] at q₂
  exact (trace_eq em.symm _ _).trans (q₁.trans (q₂.symm.trans (trace_eq en _ _)))

include laws in
theorem reduced_slide_first {A B U V : K} (f : P.sum A U ⟶ P.sum B V)
    (h : V ⟶ P.sum B U) (hf : G.guarded (P.inr ≫ f)) :
    T.toFeedback i (slideAfter f h) (slideAfter_guard f h (Or.inl hf)) =
      T.toFeedback i (slideBefore f h) (slideBefore_guard f h (Or.inl hf)) := by
  let s : TwoBody P (P.sum I A) (P.sum I I) (P.sum B I) (P.sum B I) U V :=
    ⟨P.map (P.desc (i.to A) (𝟙 A)) (𝟙 U) ≫ f ≫ P.map P.inl (𝟙 V),
      P.desc (P.desc (i.to _) (i.to _)) (h ≫ P.map P.inl (𝟙 U))⟩
  have ha : G.nested (P.inl ≫ P.inl ≫ s.first) := by
    unfold Guardedness.nested
    rw [show (P.inl ≫ P.inl ≫ s.first) ≫ P.assoc = i.to _ from i.hom_ext _ _]
    exact G.initial i
  have he : G.nested (P.inl ≫ P.inl ≫ s.second) := by
    unfold Guardedness.nested
    rw [show (P.inl ≫ P.inl ≫ s.second) ≫ P.assoc = i.to _ from i.hom_ext _ _]
    exact G.initial i
  have hu : G.nested (P.inr ≫ s.first) := by
    simpa [s, Guardedness.nested, Coproducts.map, Coproducts.assoc] using
      G.map hf (𝟙 B) (P.inr (X := I))
  let a : A ⟶ P.sum (P.sum I I) (P.sum A I) := P.inl ≫ P.inr
  let b : P.sum (P.sum B B) (P.sum I I) ⟶ B :=
    P.desc (P.desc (𝟙 B) (𝟙 B)) (P.desc (i.to B) (i.to B))
  let guards := s.slidingI_guards i ha hu he
  refine reduce_profile_eq i T laws guards.1 guards.2 (laws.slideI i s ha hu he)
    a b ?_ ?_ _ _
  · rw [TwoBody.markedCutFirst, traceBody_restore]
    apply P.hom_ext <;> simp [tighten, slideAfter, TwoBody.cutFirst, TwoBody.slideEntry,
      TwoBody.slideExit, TwoBody.firstEntry, TwoBody.secondEntry, TwoBody.firstStep,
      TwoBody.secondStep, a, b, s, Coproducts.map]
  · rw [TwoBody.markedCutSecond, traceBody_restore]
    apply P.hom_ext <;> simp [tighten, slideBefore, TwoBody.cutSecond, TwoBody.slideEntry,
      TwoBody.slideExit, TwoBody.firstEntry, TwoBody.secondEntry, TwoBody.firstStep,
      TwoBody.secondStep, a, b, s, Coproducts.map]

include laws in
theorem reduced_enterState {B U : K} (f : U ⟶ P.sum B U) (hf : G.guarded f) :
    Feedback.onBranches (T.toFeedback i) P.inr f hf =
      Feedback.iterate (T.toFeedback i) f hf := by
  let s : TwoBody P (P.sum I I) (P.sum I U) (P.sum B I) (P.sum I I) U U :=
    ⟨P.desc (P.desc (i.to _) (i.to _)) (f ≫ P.map P.inl (𝟙 U)),
      P.desc (P.desc (i.to _) P.inr) P.inr⟩
  have ha : G.nested (P.inl ≫ P.inl ≫ s.first) := by
    unfold Guardedness.nested
    rw [show (P.inl ≫ P.inl ≫ s.first) ≫ P.assoc = i.to _ from i.hom_ext _ _]
    exact G.initial i
  have hu : G.nested (P.inr ≫ s.first) := by
    simpa [s, Guardedness.nested, Coproducts.map, Coproducts.assoc] using
      G.map hf (𝟙 B) (P.inr (X := I))
  have hv : G.guarded ((P.inr ≫ s.second) ≫ externalMark) := by
    simpa [s, externalMark] using G.trivial (P.inr : U ⟶ P.sum I U)
  let a : U ⟶ P.sum (P.sum I I) (P.sum I U) := P.inr ≫ P.inr
  let b : P.sum (P.sum B I) (P.sum I I) ⟶ B :=
    P.desc (P.desc (𝟙 B) (i.to B)) (P.desc (i.to B) (i.to B))
  let guards := s.slidingII_guards i ha hu hv
  have hfb (e : U ⟶ P.sum B U) : G.FeedbackGuard (P.desc e f) := by
    simpa [FeedbackGuard] using hf
  refine reduce_profile_eq i T laws guards.1 guards.2 (laws.slideII i s ha hu hv)
    a b ?_ ?_ (hfb _) (hfb _)
  · rw [TwoBody.markedCutFirst, traceBody_restore]
    apply P.hom_ext <;> simp [tighten, TwoBody.cutFirst, TwoBody.slideEntry,
      TwoBody.slideExit, TwoBody.firstEntry, TwoBody.secondEntry, TwoBody.firstStep,
      TwoBody.secondStep, a, b, s, Coproducts.map]
  · rw [TwoBody.markedCutSecond, traceBody_restore]
    apply P.hom_ext <;> simp [tighten, TwoBody.cutSecond, TwoBody.slideEntry,
      TwoBody.slideExit, TwoBody.firstEntry, TwoBody.secondEntry, TwoBody.firstStep,
      TwoBody.secondStep, a, b, s, Coproducts.map]

include laws in
theorem reduced_slide {A B U V : K} (f : P.sum A U ⟶ P.sum B V)
    (h : V ⟶ P.sum B U) (guard : G.guarded (P.inr ≫ f) ∨ G.guarded h) :
    T.toFeedback i (slideAfter f h) (slideAfter_guard f h guard) =
      T.toFeedback i (slideBefore f h) (slideBefore_guard f h guard) := by
  rcases guard with hf | hh
  · exact reduced_slide_first i T laws f h hf
  let trace : G.Feedback := T.toFeedback i
  have formula {X R S : K} (entry : X ⟶ P.sum R S) (body : S ⟶ P.sum R S)
      (hb : G.guarded body) :
      Feedback.onBranches trace entry body hb =
        entry ≫ P.desc (𝟙 R) (Feedback.iterate trace body hb) :=
    onBranches_formula_ofRouting i (T.toFeedback_tighten i laws.tighten)
      (reduced_superpose i T laws) (reduced_enterState i T laws) entry body hb
  have onBranches_eq {X R S : K} {p : P.sum X S ⟶ P.sum R S}
      (hp : G.FeedbackGuard p) {entry : X ⟶ P.sum R S} {body : S ⟶ P.sum R S}
      (hb : G.guarded body) (e : p = P.desc entry body) :
      trace p hp = Feedback.onBranches trace entry body hb := by
    subst p
    rfl
  let g := P.inr ≫ f
  let guards := G.dinaturality_bodies g h (Or.inr hh)
  let bodyU := g ≫ P.desc P.inl h
  let bodyV := h ≫ P.desc P.inl g
  let iterU := Feedback.iterate trace bodyU guards.1
  let iterV := Feedback.iterate trace bodyV guards.2
  have h' : G.guarded (P.inr ≫ P.desc h h) := by simpa using hh
  have first := reduced_slide_first i T laws (P.desc h h) g h'
  have after : slideAfter (P.desc h h) g = P.desc bodyV bodyV := by
    simp [slideAfter, bodyV]
  have before : slideBefore (P.desc h h) g = P.desc h bodyU := by
    simp [slideBefore, bodyU]
  have eV : iterV = h ≫ P.desc (𝟙 B) iterU := by
    exact (onBranches_eq _ guards.2 after).symm.trans
      (first.trans ((onBranches_eq _ guards.1 before).trans (formula h bodyU guards.1)))
  have ep : slideAfter f h = P.desc ((P.inl ≫ f) ≫ P.desc P.inl h) bodyU := by
    apply P.hom_ext <;> simp [slideAfter, bodyU, g]
  have eq : slideBefore f h = P.desc (P.inl ≫ f) bodyV := rfl
  refine (onBranches_eq _ guards.1 ep).trans ((formula _ bodyU guards.1).trans ?_)
  refine Eq.trans ?_ ((formula _ bodyV guards.2).symm.trans (onBranches_eq _ guards.2 eq).symm)
  simp only [Category.assoc, P.desc_comp, P.inl_desc]
  change P.inl ≫ f ≫ P.desc (𝟙 B) (h ≫ P.desc (𝟙 B) iterU) =
    P.inl ≫ f ≫ P.desc (𝟙 B) iterV
  rw [eV]

end Silmaril.Calco2019.Proofs.Feedback
