module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs

/-! # Unrolling in every Elgot Freyd category

The proof uses the fixpoint, naturality and codiagonal laws of the
computation category and uniformity along pure maps only: coproduct
injections of phase objects and the map that forgets the phase.
-/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (roundsStep)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [ElgotFreydCategory J]

section Cases

variable {A B : V} {T : C}

/-- Case analysis on a pure binary sum of phases. -/
noncomputable def dJ (u : J.obj A ⟶ T) (v : J.obj B ⟶ T) : J.obj (A ⨿ B) ⟶ T :=
  (PreservesColimitPair.iso J A B).inv ≫ coprod.desc u v

@[reassoc]
theorem inl_dJ (u : J.obj A ⟶ T) (v : J.obj B ⟶ T) : J.map coprod.inl ≫ dJ J u v = u := by
  have h : J.map (coprod.inl : A ⟶ A ⨿ B) = coprod.inl ≫ (PreservesColimitPair.iso J A B).hom := by
    rw [PreservesColimitPair.iso_hom, inl_coprodComparison]
  rw [dJ, h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]

@[reassoc]
theorem inr_dJ (u : J.obj A ⟶ T) (v : J.obj B ⟶ T) : J.map coprod.inr ≫ dJ J u v = v := by
  have h : J.map (coprod.inr : B ⟶ A ⨿ B) = coprod.inr ≫ (PreservesColimitPair.iso J A B).hom := by
    rw [PreservesColimitPair.iso_hom, inr_coprodComparison]
  rw [dJ, h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]

theorem dJ_ext {f g : J.obj (A ⨿ B) ⟶ T}
    (hl : J.map coprod.inl ≫ f = J.map coprod.inl ≫ g)
    (hr : J.map coprod.inr ≫ f = J.map coprod.inr ≫ g) : f = g := by
  rw [← cancel_epi (PreservesColimitPair.iso J A B).hom]
  apply coprod.hom_ext
  · rw [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, inl_coprodComparison_assoc]
    exact hl
  · rw [PreservesColimitPair.iso_hom, inr_coprodComparison_assoc, inr_coprodComparison_assoc]
    exact hr

end Cases

/-- Eliminate the second phase object of a two-object system. The first
object runs `a` and moves to the second. The second runs `c`, which may
stay there, return to the first, or exit. -/
theorem eliminate_right {X W : V} {Y : C} (a : J.obj X ⟶ Y ⨿ J.obj W)
    (c : J.obj W ⟶ (Y ⨿ J.obj X) ⨿ J.obj W) :
    J.map coprod.inl ≫ iterate (dJ J (a ≫ coprod.map (𝟙 Y) (J.map coprod.inr))
      (c ≫ coprod.desc (coprod.map (𝟙 Y) (J.map coprod.inl)) (J.map coprod.inr ≫ coprod.inr))) =
      iterate (a ≫ coprod.desc coprod.inl (iterate c)) := by
  let ιX : J.obj X ⟶ J.obj (X ⨿ W) := J.map coprod.inl
  let ιW : J.obj W ⟶ J.obj (X ⨿ W) := J.map coprod.inr
  let f : J.obj (X ⨿ W) ⟶ (Y ⨿ J.obj (X ⨿ W)) ⨿ J.obj (X ⨿ W) :=
    dJ J (a ≫ coprod.desc (coprod.inl ≫ coprod.inl) (ιW ≫ coprod.inr))
      (c ≫ coprod.desc (coprod.desc (coprod.inl ≫ coprod.inl) (ιX ≫ coprod.inr ≫ coprod.inl))
        (ιW ≫ coprod.inr))
  have flat : f ≫ coprod.desc (𝟙 _) coprod.inr =
      dJ J (a ≫ coprod.map (𝟙 Y) ιW)
        (c ≫ coprod.desc (coprod.map (𝟙 Y) ιX) (ιW ≫ coprod.inr)) := by
    apply dJ_ext J
    · rw [inl_dJ_assoc, inl_dJ, Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp
    · rw [inr_dJ_assoc, inr_dJ, Category.assoc]
      congr 1
      apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp
      · simp
  have second : ιW ≫ iterate f = iterate c ≫ coprod.map (𝟙 Y) ιX := by
    have comm : (c ≫ coprod.map (coprod.map (𝟙 Y) ιX) (𝟙 _)) ≫ coprod.map (𝟙 _) ιW = ιW ≫ f := by
      rw [inr_dJ, Category.assoc]
      congr 1
      apply coprod.hom_ext
      · apply coprod.hom_ext <;> simp
      · simp
    rw [← ElgotFreydCategory.pure_uniformity J _ f coprod.inr comm, ElgotCategory.naturality]
  have first : ιX ≫ iterate f =
      (a ≫ coprod.desc coprod.inl (iterate c)) ≫ coprod.map (𝟙 Y) ιX := by
    rw [ElgotCategory.fixpoint f, inl_dJ_assoc, Category.assoc, Category.assoc]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp only [coprod.inr_desc_assoc, Category.assoc, coprod.inr_desc, coprod.inr_desc]
      exact second
  have outer := ElgotFreydCategory.pure_uniformity J (a ≫ coprod.desc coprod.inl (iterate c))
    (iterate f) coprod.inl first.symm
  rw [outer, ElgotCategory.codiagonal, flat]

/-- A chain of `k + 1` phases, each running `h`, with its entry and the
pure map that forgets the phase. -/
structure Chain {X : V} {Y : C} (h : J.obj X ⟶ Y ⨿ J.obj X) (k : Nat) where
  phases : V
  start : X ⟶ phases
  fold : phases ⟶ X
  step : J.obj phases ⟶ (Y ⨿ J.obj X) ⨿ J.obj phases
  start_fold : start ≫ fold = 𝟙 X
  eliminate : J.map start ≫ iterate step = roundsStep h k
  folded : step ≫ coprod.desc (𝟙 _) (J.map fold ≫ coprod.inr) = J.map fold ≫ h

variable {X : V} {Y : C} (h : J.obj X ⟶ Y ⨿ J.obj X)

noncomputable def Chain.one : Chain J h 0 where
  phases := X
  start := 𝟙 X
  fold := 𝟙 X
  step := h ≫ coprod.inl
  start_fold := Category.id_comp _
  eliminate := by
    rw [J.map_id, Category.id_comp, ElgotCategory.fixpoint, Category.assoc, coprod.inl_desc,
      Category.comp_id]
    rfl
  folded := by
    rw [Category.assoc, coprod.inl_desc, Category.comp_id, J.map_id, Category.id_comp]

/-- The second summand of the phases of a longer chain. -/
noncomputable abbrev inRest {k : Nat} (ch : Chain J h k) : J.obj ch.phases ⟶ J.obj (X ⨿ ch.phases) :=
  J.map coprod.inr

/-- Its first phase. -/
noncomputable abbrev inFirst {k : Nat} (ch : Chain J h k) : J.obj X ⟶ J.obj (X ⨿ ch.phases) :=
  J.map coprod.inl

/-- One more phase in front: it runs `h` and enters the old chain. -/
noncomputable def succStep {k : Nat} (ch : Chain J h k) :
    J.obj (X ⨿ ch.phases) ⟶ (Y ⨿ J.obj X) ⨿ J.obj (X ⨿ ch.phases) :=
  dJ J (h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (J.map ch.start ≫ inRest J h ch ≫ coprod.inr))
    (ch.step ≫ coprod.map (𝟙 _) (inRest J h ch))

theorem succ_eliminate {k : Nat} (ch : Chain J h k) :
    inFirst J h ch ≫ iterate (succStep J h ch) = roundsStep h (k + 1) := by
  have shape : succStep J h ch =
      dJ J ((h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (J.map ch.start ≫ coprod.inr)) ≫
          coprod.map (𝟙 (Y ⨿ J.obj X)) (inRest J h ch))
        ((ch.step ≫ coprod.map coprod.inl (𝟙 _)) ≫
          coprod.desc (coprod.map (𝟙 (Y ⨿ J.obj X)) (inFirst J h ch))
            (inRest J h ch ≫ coprod.inr)) := by
    unfold succStep
    congr 1
    · rw [Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp
    · rw [Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp
  have inner : (h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (J.map ch.start ≫ coprod.inr)) ≫
      coprod.desc (coprod.inl : Y ⨿ J.obj X ⟶ (Y ⨿ J.obj X) ⨿ J.obj X)
        (iterate ch.step ≫ coprod.inl) =
      (h ≫ coprod.desc coprod.inl (roundsStep h k)) ≫
        (coprod.inl : Y ⨿ J.obj X ⟶ (Y ⨿ J.obj X) ⨿ J.obj X) := by
    rw [Category.assoc, Category.assoc]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp only [coprod.inr_desc_assoc, Category.assoc, coprod.inr_desc]
      rw [← Category.assoc, ch.eliminate]
  rw [shape, eliminate_right, ← ElgotCategory.naturality, inner, ElgotCategory.fixpoint,
    Category.assoc, coprod.inl_desc, Category.comp_id]
  rfl

theorem succ_folded {k : Nat} (ch : Chain J h k) :
    succStep J h ch ≫ coprod.desc (𝟙 _) (J.map (coprod.desc (𝟙 X) ch.fold) ≫ coprod.inr) =
      J.map (coprod.desc (𝟙 X) ch.fold) ≫ h := by
  have restFold : inRest J h ch ≫ J.map (coprod.desc (𝟙 X) ch.fold) = J.map ch.fold := by
    rw [← J.map_comp, coprod.inr_desc]
  have firstFold : inFirst J h ch ≫ J.map (coprod.desc (𝟙 X) ch.fold) = 𝟙 _ := by
    rw [← J.map_comp, coprod.inl_desc, J.map_id]
  have startFold : J.map ch.start ≫ J.map ch.fold = 𝟙 _ := by
    rw [← J.map_comp, ch.start_fold, J.map_id]
  have first : inFirst J h ch ≫ succStep J h ch =
      h ≫ coprod.desc (coprod.inl ≫ coprod.inl) (J.map ch.start ≫ inRest J h ch ≫ coprod.inr) :=
    inl_dJ J _ _
  have rest : inRest J h ch ≫ succStep J h ch = ch.step ≫ coprod.map (𝟙 _) (inRest J h ch) :=
    inr_dJ J _ _
  apply dJ_ext J
  · rw [reassoc_of% first, reassoc_of% firstFold]
    conv_rhs => rw [← Category.comp_id h]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp [reassoc_of% restFold, reassoc_of% startFold]
  · rw [reassoc_of% rest, reassoc_of% restFold, ← ch.folded]
    congr 1
    apply coprod.hom_ext
    · simp
    · simp [reassoc_of% restFold]

noncomputable def Chain.succ {k : Nat} (ch : Chain J h k) : Chain J h (k + 1) where
  phases := X ⨿ ch.phases
  start := coprod.inl
  fold := coprod.desc (𝟙 X) ch.fold
  step := succStep J h ch
  start_fold := coprod.inl_desc _ _
  eliminate := succ_eliminate J h ch
  folded := succ_folded J h ch

noncomputable def chain : (k : Nat) → Chain J h k
  | 0 => Chain.one J h
  | k + 1 => (chain k).succ

/-- The loop on any number of rounds of a step on a pure state object is
the loop on one round. -/
theorem iterate_roundsStep (n : Nat) : iterate (roundsStep h n) = iterate h := by
  let ch := chain J h n
  let f : J.obj ch.phases ⟶ (Y ⨿ J.obj ch.phases) ⨿ J.obj ch.phases :=
    ch.step ≫ coprod.map (coprod.map (𝟙 Y) (J.map ch.start)) (𝟙 _)
  have inner : iterate f = iterate ch.step ≫ coprod.map (𝟙 Y) (J.map ch.start) :=
    (ElgotCategory.naturality ch.step _).symm
  have entry : roundsStep h n ≫ coprod.map (𝟙 Y) (J.map ch.start) = J.map ch.start ≫ iterate f := by
    rw [inner, ← Category.assoc, ch.eliminate]
  have startFold : J.map ch.start ≫ J.map ch.fold = 𝟙 _ := by
    rw [← J.map_comp, ch.start_fold, J.map_id]
  have cyclic : (f ≫ coprod.desc (𝟙 _) coprod.inr) ≫ coprod.map (𝟙 Y) (J.map ch.fold) =
      J.map ch.fold ≫ h := by
    rw [← ch.folded, Category.assoc, Category.assoc]
    congr 1
    apply coprod.hom_ext
    · apply coprod.hom_ext
      · simp
      · simp [reassoc_of% startFold]
    · simp
  rw [ElgotFreydCategory.pure_uniformity J _ (iterate f) ch.start entry, ElgotCategory.codiagonal,
    ElgotFreydCategory.pure_uniformity J _ h ch.fold cyclic, ← Category.assoc, ← J.map_comp,
    ch.start_fold, J.map_id, Category.id_comp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration
