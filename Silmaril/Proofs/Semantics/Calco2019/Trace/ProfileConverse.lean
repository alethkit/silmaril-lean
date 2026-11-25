module

public import Silmaril.Semantics.Calco2019.Trace.ProfileConverse.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

theorem feedbackBody_guard {I A B U : K} (i : IsInitial I)
    (f : P.sum A U ⟶ P.sum B U) (hf : G.FeedbackGuard f) :
    G.TraceGuard (FourInterfaceTrace.feedbackBody i f) := by
  apply (restore_guard_iff _).2
  constructor
  · unfold Guardedness.nested
    rw [show (P.inl ≫ P.inl ≫ tighten f (P.desc (i.to A) (𝟙 A)) P.inl) ≫ P.assoc =
      i.to _ from i.hom_ext _ _]
    exact G.initial i
  · change G.guarded ((P.inr ≫ tighten f (P.desc (i.to A) (𝟙 A)) P.inl) ≫ P.assoc)
    have e : P.map (P.inl : B ⟶ P.sum B I) (𝟙 U) ≫ P.assoc = P.map (𝟙 B) P.inr := by
      apply P.hom_ext <;> simp [Coproducts.map, Coproducts.assoc]
    simpa [tighten, Category.assoc, e, Coproducts.map, Coproducts.assoc] using G.map hf (𝟙 B) (P.inr (X := I))

private theorem unit_transport {I A B : K} (i : IsInitial I) (t : A ⟶ B) :
    P.inr ≫ (P.desc (i.to A) (𝟙 A) ≫ t ≫ P.inl) ≫ P.desc (𝟙 B) (i.to B) = t := by
  simp

theorem run_recovered {I A B C D U : K} (i : IsInitial I) (T : G.FourInterfaceTrace)
    (laws : T.Tightening) {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    (hf : G.TraceGuard f) :
    P.inr ≫ T.run (feedbackBody_guard i (traceBody f) (traceBody_guard hf)) ≫
        P.desc (𝟙 _) (i.to _) = T.run hf := by
  let a : P.sum I (P.sum A B) ⟶ P.sum A B := P.desc (i.to _) (𝟙 _)
  let b : P.sum C D ⟶ P.sum (P.sum C D) I := P.inl
  have ha : G.guarded (P.inl ≫ a) := by
    rw [show P.inl ≫ a = i.to _ from i.hom_ext _ _]
    exact G.initial i
  have hb : G.guarded (P.inl ≫ b) := G.trivial P.inl
  exact congrArg (fun t => P.inr ≫ t ≫ P.desc (𝟙 (P.sum C D)) (i.to _)) (laws a b hf ha hb)
    |>.trans (unit_transport i (T.run hf))

theorem feedback_recovered {I A B U : K} (i : IsInitial I) (T : G.Conway)
    (f : P.sum A U ⟶ P.sum B U) (hf : G.FeedbackGuard f) :
    P.inr ≫ (FourInterfaceTrace.ofConway T).run (feedbackBody_guard i f hf) ≫
        P.desc (𝟙 _) (i.to _) = T.toFixpoints.feedback f hf := by
  let a : P.sum I A ⟶ A := P.desc (i.to _) (𝟙 _)
  let b : B ⟶ P.sum B I := P.inl
  have h : (FourInterfaceTrace.ofConway T).run (feedbackBody_guard i f hf) =
      a ≫ T.toFixpoints.feedback f hf ≫ b :=
    (trace_eq (traceBody_restore _) _ (tighten_feedbackGuard f a b hf)).trans
      (feedback_tighten T f a b hf)
  exact congrArg (fun t => P.inr ≫ t ≫ P.desc (𝟙 B) (i.to _)) h
    |>.trans (unit_transport i (T.toFixpoints.feedback f hf))

theorem reduced_tighten {I A B U A' B' : K} (i : IsInitial I) (T : G.FourInterfaceTrace)
    (laws : T.Tightening) (f : P.sum A U ⟶ P.sum B U) (a : A' ⟶ A) (b : B ⟶ B')
    (hf : G.FeedbackGuard f) :
    P.inr ≫ T.run (feedbackBody_guard i (tighten f a b) (tighten_feedbackGuard f a b hf)) ≫
        P.desc (𝟙 B') (i.to B') =
      a ≫ (P.inr ≫ T.run (feedbackBody_guard i f hf) ≫ P.desc (𝟙 B) (i.to B)) ≫ b := by
  let a' := P.map (𝟙 I) a
  let b' := P.map b (𝟙 I)
  have ha : G.guarded (P.inl ≫ a') := by
    rw [show P.inl ≫ a' = i.to _ from i.hom_ext _ _]
    exact G.initial i
  have hb : G.guarded (P.inl ≫ b') := by
    simpa [b', Coproducts.map] using G.trivial b
  have e : traceTighten (FourInterfaceTrace.feedbackBody i f) a' b' =
      FourInterfaceTrace.feedbackBody i (tighten f a b) := by
    unfold traceTighten FourInterfaceTrace.feedbackBody
    rw [traceBody_restore]
    congr 1
    unfold tighten
    apply P.hom_ext
    · apply P.hom_ext
      · exact i.hom_ext _ _
      · simp [a', b', Coproducts.map]
    · simp [a', b', Coproducts.map]
  have h := laws a' b' (feedbackBody_guard i f hf) ha hb
  have hre : T.run (traceTighten_guard a' b' (feedbackBody_guard i f hf) ha hb) =
      T.run (feedbackBody_guard i (tighten f a b) (tighten_feedbackGuard f a b hf)) := by
    generalize traceTighten_guard a' b' (feedbackBody_guard i f hf) ha hb = h₁
    generalize feedbackBody_guard i (tighten f a b) (tighten_feedbackGuard f a b hf) = h₂
    revert h₁
    rw [e]
    intros
    rfl
  rw [← hre, h]
  have post : b' ≫ P.desc (𝟙 B') (i.to B') = P.desc (𝟙 B) (i.to B) ≫ b := by
    apply P.hom_ext
    · simp [b', Coproducts.map]
    · exact i.hom_ext _ _
  simp [a', Coproducts.map, ← Category.assoc]
  simp [← post, Category.assoc]

/-- The unit padding in the restriction is independent of the chosen initial object. -/
theorem reduced_initial_independent {I J A B U : K} (i : IsInitial I) (j : IsInitial J)
    (T : G.FourInterfaceTrace) (laws : T.Tightening)
    (f : P.sum A U ⟶ P.sum B U) (hf : G.FeedbackGuard f) :
    P.inr ≫ T.run (feedbackBody_guard i f hf) ≫ P.desc (𝟙 B) (i.to B) =
      P.inr ≫ T.run (feedbackBody_guard j f hf) ≫ P.desc (𝟙 B) (j.to B) := by
  let a : P.sum I A ⟶ A := P.desc (i.to A) (𝟙 A)
  let b : B ⟶ P.sum B I := P.inl
  have normalized : traceBody (FourInterfaceTrace.feedbackBody i f) = tighten f a b :=
    traceBody_restore _
  have recover : T.run (feedbackBody_guard i f hf) =
      P.inr ≫ T.run (feedbackBody_guard j (tighten f a b) (tighten_feedbackGuard f a b hf)) ≫
        P.desc (𝟙 (P.sum B I)) (j.to _) := by
    refine (run_recovered j T laws (feedbackBody_guard i f hf)).symm.trans ?_
    generalize traceBody_guard (feedbackBody_guard i f hf) = h
    revert h
    rw [normalized]
    intro _
    rfl
  exact congrArg (fun t => P.inr ≫ t ≫ P.desc (𝟙 B) (i.to B))
    (recover.trans (reduced_tighten j T laws f a b hf))
      |>.trans (unit_transport i _)

end Silmaril.Calco2019.Proofs.Feedback
