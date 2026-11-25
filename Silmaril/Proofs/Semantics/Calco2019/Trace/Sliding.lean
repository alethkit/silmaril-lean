module

public import Silmaril.Semantics.Calco2019.Trace.Sliding.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (h : V ⟶ P.sum B U)
  (guard : G.guarded (P.inr ≫ f) ∨ G.guarded h)

theorem slideAfter_branch :
    P.inr ≫ Guardedness.slideAfter f h = (P.inr ≫ f) ≫ P.desc P.inl h := by
  simp [Guardedness.slideAfter]

theorem slideBefore_branch :
    P.inr ≫ Guardedness.slideBefore f h = h ≫ P.desc P.inl (P.inr ≫ f) :=
  P.inr_desc _ _

include guard in
theorem slideAfter_guard : G.FeedbackGuard (Guardedness.slideAfter f h) := by
  change G.guarded (P.inr ≫ Guardedness.slideAfter f h)
  rw [slideAfter_branch]
  exact (G.dinaturality_bodies _ _ guard).1

include guard in
theorem slideBefore_guard : G.FeedbackGuard (Guardedness.slideBefore f h) := by
  change G.guarded (P.inr ≫ Guardedness.slideBefore f h)
  rw [slideBefore_branch]
  exact (G.dinaturality_bodies _ _ guard).2

include guard in
theorem slide_shared (F : G.Conway)
    (ha : G.FeedbackGuard (Guardedness.slideAfter f h))
    (hb : G.FeedbackGuard (Guardedness.slideBefore f h)) :
    F.toFixpoints.feedback (Guardedness.slideAfter f h) ha =
      F.toFixpoints.feedback (Guardedness.slideBefore f h) hb := by
  let g := P.inr ≫ f
  have bodies := G.dinaturality_bodies g h guard
  let s := F.iterate (g ≫ P.desc P.inl h) bodies.1
  let t := F.iterate (h ≫ P.desc P.inl g) bodies.2
  have relation : t = h ≫ P.desc (𝟙 B) s :=
    F.dinaturality h g (Or.symm guard) bodies.2 bodies.1
  change P.inl ≫ Guardedness.slideAfter f h ≫ P.desc (𝟙 B) _ =
    P.inl ≫ Guardedness.slideBefore f h ≫ P.desc (𝟙 B) _
  rw [iterate_eq F.toFixpoints (slideAfter_branch f h) ha bodies.1,
    iterate_eq F.toFixpoints (slideBefore_branch f h) hb bodies.2]
  change P.inl ≫ (f ≫ P.desc P.inl h) ≫ P.desc (𝟙 B) s =
    P.inl ≫ Guardedness.slideBefore f h ≫ P.desc (𝟙 B) t
  rw [← Category.assoc (P.inl : A ⟶ P.sum A V)]
  change P.inl ≫ (f ≫ P.desc P.inl h) ≫ P.desc (𝟙 B) s =
    (P.inl ≫ P.desc (P.inl ≫ f) _) ≫ P.desc (𝟙 B) t
  simp [Category.assoc, relation]

end Silmaril.Calco2019.Proofs.Feedback
