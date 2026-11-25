module

public import Silmaril.Semantics.Calco2019.Trace.Defs

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

private theorem inl_map {A B U V : K} (f : A ⟶ B) (g : U ⟶ V) :
    P.inl ≫ P.map f g = f ≫ P.inl := P.inl_desc _ _

private theorem inr_map {A B U V : K} (f : A ⟶ B) (g : U ⟶ V) :
    P.inr ≫ P.map f g = g ≫ P.inr := P.inr_desc _ _

theorem iterate_eq (F : G.Fixpoints) {U B : K} {f g : U ⟶ P.sum B U}
    (e : f = g) (hf : G.guarded f) (hg : G.guarded g) :
    F.iterate f hf = F.iterate g hg := by
  subst g
  rfl

theorem recover (F : G.Fixpoints) {U B : K} (f : U ⟶ P.sum B U) (hf : G.guarded f) :
    Guardedness.Feedback.iterate (F.feedback) f hf = F.iterate f hf := by
  let body := P.desc f f
  have hbody : G.guarded (P.inr ≫ body) := by simpa [body] using hf
  let sol := F.iterate (P.inr ≫ body) hbody
  have fix : (P.inr ≫ body) ≫ P.desc (𝟙 B) sol = sol := F.fixpoint _ _
  change P.inl ≫ body ≫ P.desc (𝟙 B) sol = _
  rw [← Category.assoc, P.inl_desc]
  refine (?_ : f ≫ P.desc (𝟙 B) sol = sol).trans ?_
  · simpa [body] using fix
  · exact iterate_eq F (P.inr_desc _ _) hbody hf

theorem tighten_guard {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') (hf : G.FeedbackGuard f) :
    G.FeedbackGuard (Guardedness.tighten f a b) := by
  change G.guarded (P.inr ≫ P.map a (𝟙 U) ≫ f ≫ P.map b (𝟙 U))
  rw [← Category.assoc (P.inr : U ⟶ P.sum A' U), inr_map, Category.id_comp, ← Category.assoc]
  exact G.map hf b (𝟙 U)

theorem tighten (F : G.Conway) {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') (hf : G.FeedbackGuard f) :
    F.toFixpoints.feedback (Guardedness.tighten f a b) (tighten_guard f a b hf) =
      a ≫ F.toFixpoints.feedback f hf ≫ b := by
  let L := Guardedness.tighten f a b
  have left : P.inl ≫ L = a ≫ P.inl ≫ f ≫ P.map b (𝟙 U) := by
    change P.inl ≫ (P.map a (𝟙 U) ≫ f ≫ P.map b (𝟙 U)) = _
    rw [← Category.assoc, inl_map, Category.assoc]
  have right : P.inr ≫ L = (P.inr ≫ f) ≫ P.map b (𝟙 U) := by
    change P.inr ≫ (P.map a (𝟙 U) ≫ f ≫ P.map b (𝟙 U)) = _
    rw [← Category.assoc, inr_map, Category.id_comp, Category.assoc]
  have inner : F.iterate (P.inr ≫ L) (tighten_guard f a b hf) =
      F.iterate (P.inr ≫ f) hf ≫ b := by
    exact (iterate_eq F.toFixpoints right _ (G.map hf b (𝟙 U))).trans
      (F.naturalCodiagonal.naturality _ _ hf (G.map hf b (𝟙 U)))
  change P.inl ≫ L ≫ P.desc (𝟙 B') (F.iterate (P.inr ≫ L) _) =
    a ≫ (P.inl ≫ f ≫ P.desc (𝟙 B) (F.iterate (P.inr ≫ f) hf)) ≫ b
  rw [inner, ← Category.assoc (P.inl : A' ⟶ P.sum A' U), left]
  simp only [Category.assoc, P.map_desc, Category.comp_id, Category.id_comp, P.desc_comp]

theorem yanking (F : G.Fixpoints) (U : K) :
    F.feedback (P.swap (X := U) (Y := U)) (by
      change G.guarded (P.inr ≫ P.swap (X := U) (Y := U))
      simpa [Coproducts.swap] using G.trivial (X := U) (Y := U) (Z := U) (𝟙 U)) = 𝟙 U := by
  let f := P.swap (X := U) (Y := U)
  have hf : G.FeedbackGuard f := by
    change G.guarded (P.inr ≫ P.swap (X := U) (Y := U))
    simpa [Coproducts.swap] using G.trivial (X := U) (Y := U) (Z := U) (𝟙 U)
  let sol := F.iterate (P.inr ≫ f) hf
  have fix : (P.inr ≫ f) ≫ P.desc (𝟙 U) sol = sol := F.fixpoint _ _
  change P.inl ≫ f ≫ P.desc (𝟙 U) sol = _
  have e : 𝟙 U = sol := by simpa [f, Coproducts.swap] using fix
  simpa [f, Coproducts.swap] using e.symm


private theorem slide_right {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (q : V ⟶ U) :
    P.inr ≫ (f ≫ P.map (𝟙 B) q) =
      (P.inr ≫ f) ≫ P.desc P.inl (q ≫ P.inr) := by
  simp [Coproducts.map]

private theorem slide_left {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (q : V ⟶ U) :
    P.inr ≫ (P.map (𝟙 A) q ≫ f) =
      (q ≫ P.inr) ≫ P.desc P.inl (P.inr ≫ f) := by
  simp [Coproducts.map]

theorem slide_guards {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (q : V ⟶ U)
    (hf : G.guarded (P.inr ≫ f) ∨ G.guarded (q ≫ (P.inr : U ⟶ P.sum B U))) :
    G.FeedbackGuard (f ≫ P.map (𝟙 B) q) ∧
      G.FeedbackGuard (P.map (𝟙 A) q ≫ f) := by
  have e := G.dinaturality_bodies (P.inr ≫ f) (q ≫ P.inr) hf
  constructor
  · change G.guarded (P.inr ≫ (f ≫ P.map (𝟙 B) q))
    rw [slide_right]
    exact e.1
  · change G.guarded (P.inr ≫ (P.map (𝟙 A) q ≫ f))
    rw [slide_left]
    exact e.2

theorem slide (F : G.Conway) {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (q : V ⟶ U)
    (hf : G.guarded (P.inr ≫ f) ∨ G.guarded (q ≫ (P.inr : U ⟶ P.sum B U)))
    (hl : G.FeedbackGuard (f ≫ P.map (𝟙 B) q)) (hr : G.FeedbackGuard (P.map (𝟙 A) q ≫ f)) :
    F.toFixpoints.feedback (f ≫ P.map (𝟙 B) q) hl =
      F.toFixpoints.feedback (P.map (𝟙 A) q ≫ f) hr := by
  let g := P.inr ≫ f
  let h : V ⟶ P.sum B U := q ≫ P.inr
  let e := G.dinaturality_bodies g h hf
  let s := F.iterate (g ≫ P.desc P.inl h) e.1
  let t := F.iterate (h ≫ P.desc P.inl g) e.2
  have eqL := iterate_eq F.toFixpoints (slide_right f q) hl e.1
  have eqR := iterate_eq F.toFixpoints (slide_left f q) hr e.2
  have relation : t = q ≫ s := by
    have d := F.dinaturality h g (Or.symm hf) e.2 e.1
    change t = (q ≫ P.inr) ≫ P.desc (𝟙 B) s at d
    simpa only [Category.assoc, P.inr_desc] using d
  change P.inl ≫ (f ≫ P.map (𝟙 B) q) ≫ P.desc (𝟙 B) _ =
    P.inl ≫ (P.map (𝟙 A) q ≫ f) ≫ P.desc (𝟙 B) _
  rw [eqL, eqR]
  change P.inl ≫ (f ≫ P.map (𝟙 B) q) ≫ P.desc (𝟙 B) s =
    P.inl ≫ (P.map (𝟙 A) q ≫ f) ≫ P.desc (𝟙 B) t
  have entry : P.inl ≫ (P.map (𝟙 A) q ≫ f) = P.inl ≫ f := by
    rw [← Category.assoc, inl_map, Category.id_comp]
  calc
    _ = (P.inl ≫ f) ≫ P.desc (𝟙 B) (q ≫ s) := by
      simp only [Category.assoc, P.map_desc, Category.id_comp]
    _ = _ := by rw [← relation, ← entry, Category.assoc]


theorem vanishing_initial_guard {A B I : K} (i : IsInitial I)
    (f : P.sum A I ⟶ P.sum B I) : G.FeedbackGuard f := by
  change G.guarded (P.inr ≫ f)
  rw [i.hom_ext (P.inr ≫ f) (i.to (P.sum B I))]
  exact G.initial i

theorem vanishing_initial (F : G.Fixpoints) {A B I : K} (i : IsInitial I)
    (f : P.sum A I ⟶ P.sum B I) (hf : G.FeedbackGuard f) :
    F.feedback f hf = P.inl ≫ f ≫ P.desc (𝟙 B) (i.to B) :=
  congrArg (fun s => P.inl ≫ f ≫ P.desc (𝟙 B) s) (i.hom_ext _ _)

theorem superpose_guard {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (g : A' ⟶ B') (hf : G.FeedbackGuard f) :
    G.FeedbackGuard (Guardedness.superpose f g) := by
  change G.guarded (P.inr ≫ Guardedness.superpose f g)
  rw [Guardedness.superpose, P.inr_desc, ← Category.assoc]
  exact G.map hf P.inl (𝟙 U)

theorem superpose (F : G.Conway) {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (g : A' ⟶ B') (hf : G.FeedbackGuard f) (h : G.FeedbackGuard (Guardedness.superpose f g)) :
    F.toFixpoints.feedback (Guardedness.superpose f g) h =
      P.map (F.toFixpoints.feedback f hf) g := by
  let L := Guardedness.superpose f g
  have right : P.inr ≫ L = (P.inr ≫ f) ≫ P.map (P.inl : B ⟶ P.sum B B') (𝟙 U) := by
    change P.inr ≫ Guardedness.superpose f g = _
    rw [Guardedness.superpose, P.inr_desc, Category.assoc]
  have inner : F.iterate (P.inr ≫ L) h = F.iterate (P.inr ≫ f) hf ≫ P.inl :=
    (iterate_eq F.toFixpoints right h (G.map hf P.inl (𝟙 U))).trans
      (F.naturalCodiagonal.naturality _ _ hf (G.map hf P.inl (𝟙 U)))
  change P.inl ≫ L ≫ P.desc (𝟙 (P.sum B B')) _ = _
  rw [inner]
  change P.inl ≫ Guardedness.superpose f g ≫ _ = _
  simp only [Guardedness.superpose, P.desc_comp, Coproducts.map, Guardedness.Fixpoints.feedback,
    Category.assoc, P.inl_desc, P.inr_desc, Category.comp_id, Category.id_comp]

end Silmaril.Calco2019.Proofs.Feedback
