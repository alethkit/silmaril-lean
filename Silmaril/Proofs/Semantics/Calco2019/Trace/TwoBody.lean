module

public import Silmaril.Semantics.Calco2019.Trace.TwoBody.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A E B D U V : K} (c : TwoBody P A E B D U V)
  (guard : G.guarded (P.inr ≫ c.first) ∨ G.guarded (P.inr ≫ c.second))

include guard in
theorem cuts_guarded : G.FeedbackGuard c.cutFirst ∧ G.FeedbackGuard c.cutSecond := by
  have g : G.guarded c.firstStep ∨ G.guarded c.secondStep :=
    guard.imp (fun h => by simpa [TwoBody.firstStep, Category.assoc] using G.map h P.inl (𝟙 V))
      (fun h => by simpa [TwoBody.secondStep, Category.assoc] using G.map h P.inr (𝟙 U))
  have h := G.dinaturality_bodies c.firstStep c.secondStep g
  exact ⟨by simpa [TwoBody.cutFirst, FeedbackGuard] using h.1,
    by simpa [TwoBody.cutSecond, FeedbackGuard] using h.2⟩

include guard in
theorem slideTwoBodies (F : G.Conway)
    (hf : G.FeedbackGuard c.cutFirst) (hs : G.FeedbackGuard c.cutSecond) :
    F.toFixpoints.feedback c.cutFirst hf = F.toFixpoints.feedback c.cutSecond hs := by
  have g : G.guarded c.firstStep ∨ G.guarded c.secondStep :=
    guard.imp (fun h => by simpa [TwoBody.firstStep, Category.assoc] using G.map h P.inl (𝟙 V))
      (fun h => by simpa [TwoBody.secondStep, Category.assoc] using G.map h P.inr (𝟙 U))
  have h := G.dinaturality_bodies c.firstStep c.secondStep g
  let first := c.firstStep ≫ P.desc P.inl c.secondStep
  let second := c.secondStep ≫ P.desc P.inl c.firstStep
  let s := F.iterate first h.1
  let t := F.iterate second h.2
  have s_eq : s = c.firstStep ≫ P.desc (𝟙 (P.sum B D)) t :=
    F.dinaturality _ _ g h.1 h.2
  have t_eq : t = c.secondStep ≫ P.desc (𝟙 (P.sum B D)) s :=
    F.dinaturality _ _ (Or.symm g) h.2 h.1
  have first_step : P.inr ≫ c.cutFirst = first := P.inr_desc _ _
  have second_step : P.inr ≫ c.cutSecond = second := P.inr_desc _ _
  change P.inl ≫ c.cutFirst ≫ P.desc (𝟙 (P.sum B D)) (F.iterate (P.inr ≫ c.cutFirst) hf) =
    P.inl ≫ c.cutSecond ≫ P.desc (𝟙 (P.sum B D)) (F.iterate (P.inr ≫ c.cutSecond) hs)
  refine (congrArg (fun q => P.inl ≫ c.cutFirst ≫ P.desc (𝟙 (P.sum B D)) q)
    (iterate_eq F.toFixpoints first_step hf h.1)).trans ?_
  refine Eq.trans ?_ (congrArg (fun q => P.inl ≫ c.cutSecond ≫ P.desc (𝟙 (P.sum B D)) q)
    (iterate_eq F.toFixpoints second_step hs h.2)).symm
  rw [show P.inl ≫ c.cutFirst ≫ P.desc (𝟙 (P.sum B D)) s =
      P.desc (c.firstEntry ≫ P.desc P.inl c.secondStep) c.secondEntry ≫ P.desc (𝟙 (P.sum B D)) s by
    rw [← Category.assoc, TwoBody.cutFirst, P.inl_desc],
    show P.inl ≫ c.cutSecond ≫ P.desc (𝟙 (P.sum B D)) t =
      P.desc c.firstEntry (c.secondEntry ≫ P.desc P.inl c.firstStep) ≫ P.desc (𝟙 (P.sum B D)) t by
    rw [← Category.assoc, TwoBody.cutSecond, P.inl_desc]]
  simp only [P.desc_comp, Category.assoc, P.inl_desc]
  rw [← t_eq, ← s_eq]

include guard in
theorem slideTwoBodies_lawful {trace : G.Feedback} [HasInitial K] (laws : Feedback.Lawful trace) :
    trace c.cutFirst (cuts_guarded c guard).1 = trace c.cutSecond (cuts_guarded c guard).2 := by
  let F := Feedback.conway laws
  have h := slideTwoBodies c guard F (cuts_guarded c guard).1 (cuts_guarded c guard).2
  change (Feedback.fixpoints laws.toLocalLaws).feedback c.cutFirst _ =
    (Feedback.fixpoints laws.toLocalLaws).feedback c.cutSecond _ at h
  exact (Feedback.fixpoints_feedback laws.toLocalLaws _ _).symm.trans
    (h.trans (Feedback.fixpoints_feedback laws.toLocalLaws _ _))

end Silmaril.Calco2019.Proofs.Feedback
