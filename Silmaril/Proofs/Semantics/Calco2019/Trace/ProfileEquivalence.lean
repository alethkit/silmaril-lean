module

public import Silmaril.Semantics.Calco2019.Trace.ProfileEquivalence.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileLaws
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

theorem profile_run_eq (T : G.FourInterfaceTrace) {A B C D U : K}
    {f g : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    (e : f = g) (hf : G.TraceGuard f) (hg : G.TraceGuard g) :
    T.run hf = T.run hg := by
  subst g
  rfl

theorem vanish_pair_ofConway (F : G.Conway) {A B C D U V : K}
    (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)
    (hf : G.TraceGuard s.flatTraceBody) :
    (FourInterfaceTrace.ofConway F).run hf =
      (FourInterfaceTrace.ofConway F).run ((FourInterfaceTrace.ofConway F).guarded
        (s.innerTraceBody_guard hf)) := by
  let T := FourInterfaceTrace.ofConway F
  have e : T.run (s.innerTraceBody_guard hf) = s.stagedTraceBody F.toFixpoints :=
    s.innerTraceBody_eq_staged F.toFixpoints (s.innerTraceBody_guard hf)
      (F.naturalCodiagonal.naturality s.second P.assoc s.second_guard _)
  exact (s.guardedTrace_vanish_pair F hf).trans
    (profile_run_eq T e.symm (s.stagedTraceBody_guard F hf) _)

theorem profile_ext {T S : G.FourInterfaceTrace}
    (h : ∀ {A B C D U : K} {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
      (hf : G.TraceGuard f), T.run hf = S.run hf) : T = S := by
  cases T
  cases S
  congr
  funext A B C D U f hf
  exact h hf

theorem conway_of_profile_feedback [HasInitial K] {I : K} (i : IsInitial I) (F : G.Conway)
    (laws : Feedback.Lawful ((FourInterfaceTrace.ofConway F).toFeedback i)) :
    Feedback.conway laws = F := by
  let recover := fun t : {tr : G.Feedback // Feedback.Lawful tr} => Feedback.conway t.property
  have e : (⟨(FourInterfaceTrace.ofConway F).toFeedback i, laws⟩ :
      {tr : G.Feedback // Feedback.Lawful tr}) = ⟨F.toFixpoints.feedback, Feedback.lawful_ofConway F⟩ :=
    Subtype.ext (FourInterfaceTrace.toFeedback_ofConway i F)
  exact (congrArg recover e).trans (Feedback.conway_of_feedback F)

variable [HasInitial K] {I : K} (i : IsInitial I) (T : G.FourInterfaceTrace) (laws : T.Lawful)

include laws in
theorem reduced_vanish_pair : Feedback.PairVanishing (T.toFeedback i) := by
  intro A B U V s h
  let tr : G.Feedback := T.toFeedback i
  let loc : Feedback.LocalLaws tr := T.toFeedback_localLaws i laws.toLocalLaws
  let F : G.Fixpoints := Feedback.fixpoints loc
  let pad : P.sum (P.sum B U) V ⟶ P.sum (P.sum (P.sum B I) U) V :=
    P.map (P.map P.inl (𝟙 U)) (𝟙 V)
  have pad_assoc : pad ≫ P.assoc = P.assoc ≫ P.map (P.inl : B ⟶ P.sum B I) (𝟙 (P.sum U V)) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [pad, Coproducts.map, Coproducts.assoc]
    · simp [pad, Coproducts.map, Coproducts.assoc]
  let s' : TwoStateBody G (P.sum I A) (P.sum B I) U V :=
    ⟨P.desc (i.to A) (𝟙 A) ≫ s.entry ≫ pad, s.first ≫ pad, s.second ≫ pad, by
      change G.guarded (P.desc (s.first ≫ pad) (s.second ≫ pad) ≫ P.assoc)
      rw [← P.desc_comp, Category.assoc, pad_assoc, ← Category.assoc]
      exact G.map s.guarded P.inl (𝟙 (P.sum U V))⟩
  have hflat : G.TraceGuard s'.flatTraceBody := by
    apply (restore_guard_iff _).2
    constructor
    · unfold Guardedness.nested
      rw [show (P.inl ≫ P.inl ≫ P.desc (s'.entry ≫ P.assoc)
        (P.desc s'.first s'.second ≫ P.assoc)) ≫ P.assoc = i.to _ from i.hom_ext _ _]
      exact G.initial i
    · have reassoc : P.map (P.inl : B ⟶ P.sum B I) (𝟙 (P.sum U V)) ≫ P.assoc =
          P.map (𝟙 B) (P.inr : P.sum U V ⟶ P.sum I (P.sum U V)) := by
        apply P.hom_ext <;> simp [Coproducts.map, Coproducts.assoc]
      change G.guarded ((P.inr ≫ P.desc (s'.entry ≫ P.assoc)
        (P.desc s'.first s'.second ≫ P.assoc)) ≫ P.assoc)
      rw [P.inr_desc]
      change G.guarded ((P.desc (s.first ≫ pad) (s.second ≫ pad) ≫ P.assoc) ≫ P.assoc)
      have ep : pad ≫ P.assoc ≫ P.assoc =
          P.assoc ≫ P.map (𝟙 B) (P.inr : P.sum U V ⟶ P.sum I (P.sum U V)) := by
        rw [← Category.assoc, pad_assoc, Category.assoc, reassoc]
      rw [← P.desc_comp]
      simpa only [Category.assoc, ep] using G.map s.guarded (𝟙 B) (P.inr (X := I))
  have runF {A₁ B₁ C₁ D₁ W : K}
      {f : P.sum (P.sum A₁ W) B₁ ⟶ P.sum C₁ (P.sum D₁ W)}
      (hf : G.TraceGuard f) : F.guardedTrace hf = T.run hf :=
    (Feedback.fixpoints_feedback loc _ (traceBody_guard hf)).trans (T.toFeedback_run i laws.tighten hf)
  have stage : T.run (s'.innerTraceBody_guard hflat) = s'.stagedTraceBody F :=
    (runF _).symm.trans (s'.innerTraceBody_eq_staged F _
      (Feedback.iterate_natural loc s'.second P.assoc s'.second_guard
        (G.map s'.second_guard P.assoc (𝟙 V))))
  have hstage : G.TraceGuard (s'.stagedTraceBody F) := stage ▸ T.guarded (s'.innerTraceBody_guard hflat)
  have diagram : T.run hflat = T.run hstage := (laws.vanishPair s' hflat).trans
    (profile_run_eq T stage _ hstage)
  let a : A ⟶ P.sum I A := P.inr
  let b : P.sum B I ⟶ B := P.desc (𝟙 B) (i.to B)
  let v := F.iterate s.second s.second_guard
  let finish := P.desc (𝟙 (P.sum B U)) v
  have h₂ : F.iterate s'.second s'.second_guard = v ≫ P.map (P.inl : B ⟶ P.sum B I) (𝟙 U) :=
    Feedback.iterate_natural loc s.second (P.map P.inl (𝟙 U)) s.second_guard s'.second_guard
  have eq_flat : tighten (traceBody s'.flatTraceBody) a b =
      P.desc (s.entry ≫ P.assoc) (P.desc s.first s.second ≫ P.assoc) := by
    rw [TwoStateBody.flatTraceBody, traceBody_restore]
    apply P.hom_ext
    · simp [tighten, s', a, b, pad_assoc, Coproducts.map]
    · simp [tighten, s', a, b, pad_assoc, Coproducts.map]
  have eq_stage : tighten (traceBody (s'.stagedTraceBody F)) a b =
      P.desc (s.entry ≫ finish) (s.first ≫ finish) := by
    rw [TwoStateBody.stagedTraceBody, traceBody_restore, h₂]
    apply P.hom_ext <;> simp [tighten, s', a, b, pad, finish, Coproducts.map]
  have h₁ {X W : K} (e : X ⟶ P.sum B W) (f : W ⟶ P.sum B W) (hf : G.guarded f) :
      G.FeedbackGuard (P.desc e f) := by simpa [FeedbackGuard] using hf
  exact reduce_profile_eq i T laws.toLocalLaws hflat hstage diagram a b eq_flat eq_stage
    (h₁ _ _ s.guarded) (h₁ _ _ h)

end Silmaril.Calco2019.Proofs.Feedback
