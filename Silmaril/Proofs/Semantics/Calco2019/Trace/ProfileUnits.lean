module

public import Silmaril.Semantics.Calco2019.Trace.ProfileUnits.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

theorem traceInterchange_guard {I U : K} (i : IsInitial I) :
    G.TraceGuard (traceInterchange (P := P) (U := U) i) := by
  apply (restore_guard_iff _).2
  constructor
  · let a : I ⟶ P.sum U (P.sum I U) :=
      (P.inl ≫ P.inl ≫ tighten (P.swap (X := U) (Y := U))
        (P.desc (i.to U) (𝟙 U)) (P.inl (Y := I))) ≫ P.assoc
    change G.guarded a
    rw [i.hom_ext a (i.to (P.sum U (P.sum I U)))]
    exact G.initial i
  · change G.guarded ((P.inr ≫ tighten (P.swap (X := U) (Y := U))
      (P.desc (i.to U) (𝟙 U)) (P.inl (Y := I))) ≫ P.assoc)
    rw [Category.assoc]
    have h : P.inr ≫ tighten (P.swap (X := U) (Y := U))
        (P.desc (i.to U) (𝟙 U)) (P.inl (Y := I)) ≫ P.assoc =
        (P.inl : U ⟶ P.sum U (P.sum I U)) := by
      simp [tighten, Coproducts.swap, Coproducts.map, Coproducts.assoc]
    rw [h]
    simpa using G.trivial (𝟙 U)

theorem profile_yank (F : G.Conway) {I U : K} (i : IsInitial I) :
    F.toFixpoints.guardedTrace (traceInterchange_guard (G := G) (U := U) i) =
      P.desc (i.to U) (𝟙 U) ≫ (P.inl : U ⟶ P.sum U I) := by
  let a := P.desc (i.to U) (𝟙 U)
  let b : U ⟶ P.sum U I := P.inl
  let f := P.swap (X := U) (Y := U)
  have h : G.FeedbackGuard f := by
    change G.guarded (P.inr ≫ f)
    simpa [f, Coproducts.swap] using G.trivial (X := U) (Y := U) (Z := U) (𝟙 U)
  have e : traceBody (traceInterchange (P := P) (U := U) i) = tighten f a b :=
    traceBody_restore _
  change F.toFixpoints.feedback (traceBody (traceInterchange (P := P) (U := U) i)) _ = a ≫ b
  refine (trace_eq e _ (tighten_feedbackGuard f a b h)).trans ?_
  rw [feedback_tighten F f a b h]
  have e' : F.toFixpoints.feedback f h = 𝟙 U := feedback_yank F.toFixpoints U
  rw [e', Category.id_comp]

theorem profile_vanish_initial (F : G.Fixpoints) {A B C D I : K} (i : IsInitial I)
    {f : P.sum (P.sum A I) B ⟶ P.sum C (P.sum D I)} (hf : G.TraceGuard f) :
    F.guardedTrace hf = deleteInitialFeedback i f := by
  let h := traceBody f
  change F.feedback h (traceBody_guard hf) = _
  refine (feedback_vanish_initial F i h).trans ?_
  have collapse : P.assocInv ≫ P.desc (𝟙 (P.sum C D)) (i.to (P.sum C D)) =
      P.map (𝟙 C) (P.desc (𝟙 D) (i.to D)) := by
    apply P.hom_ext
    · simp [Coproducts.assocInv, Coproducts.map]
    · apply P.hom_ext
      · simp [Coproducts.assocInv, Coproducts.map]
      · exact i.hom_ext _ _
  apply P.hom_ext
  · simp [h, traceBody, deleteInitialFeedback, collapse]
  · simp [h, traceBody, deleteInitialFeedback, collapse]

end Silmaril.Calco2019.Proofs.Feedback
