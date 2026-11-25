module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.FiniteSquare.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Observation.Thms

/-! # Reflection by literal comparison of the reachable rows -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.FiniteSquare

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithConstructorSequencing Paper.WithConstructorSequencing.FiniteSquare
open Paper.TypeCategory CategoryTheory CategoryTheory.Limits
open Paper.BoundSimulation (boundReturn)
open scoped Paper.BoundSimulation.Obstruction

local notation "obj" => ofType (Φ := Empty)
set_option backward.isDefEq.respectTransparency false
private def outputTerm : Option (Option Bool) → Tm Empty
  | none => .inl .unit
  | some none => .inr (.inr .unit)
  | some (some false) => .inr (.inl (.inl .unit))
  | some (some true) => .inr (.inl (.inr .unit))

private theorem outputValue (Γ : VCtx (Ty Empty)) (o : Option (Option Bool)) :
    Tm.BranchValue Γ (outputTerm o) (Silmaril.coprod U D) := by
  rcases o with _ | (_ | (_ | _))
  · exact .inl .unit
  · exact .inr (.inr .unit)
  · exact .inr (.inl (.inl .unit))
  · exact .inr (.inl (.inr .unit))

private theorem targetOutput_exact (o : Option (Option Bool)) :
    targetOutput o = ofRegion (.br (ℓ := 0) rfl (outputValue [U] o)) ≫ (sumIso U D).hom := by
  rcases o with _ | (_ | (_ | _))
  · simp only [targetOutput]
    rw [← sumCofan_inl_sumIso_hom U D, ← Category.assoc, sumCofan_inl]
    rfl
  · simp only [targetOutput]
    rw [← sumCofan_inr_sumIso_hom U D, ← Category.assoc, sumCofan_inr]
    rfl
  · simp only [targetOutput]
    rw [← sumCofan_inr_sumIso_hom U D, ← Category.assoc, ← Category.assoc, sumCofan_inr]
    rfl
  · simp only [targetOutput]
    rw [← sumCofan_inr_sumIso_hom U D, ← Category.assoc, ← Category.assoc, sumCofan_inr]
    rfl

private theorem targetOutput_injective {o o' : Option (Option Bool)}
    (h : projection.map (targetOutput o) = projection.map (targetOutput o')) : o = o' := by
  rw [targetOutput_exact o, targetOutput_exact o', Functor.map_comp, Functor.map_comp] at h
  have h' := (cancel_mono (projection.map (sumIso U D).hom)).mp h
  have e := (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (.br (ℓ := 0) rfl (outputValue [U] o)) (.br (ℓ := 0) rfl (outputValue [U] o'))).mp h'
  have payload := Paper.BoundSimulation.Obstruction.PairSequencing.closed_branch_injective
    (outputValue [] o) (outputValue [] o') e
  rcases o with _ | (_ | (_ | _)) <;> rcases o' with _ | (_ | (_ | _)) <;>
    first | rfl | cases payload

private theorem sourceOutput_post (o : Option Bool) :
    sourceOutput o ≫ coprod.map (𝟙 (obj U)) embedding = targetOutput (o.map some) := by
  cases o <;> simp [sourceOutput, targetOutput]

private theorem table_left {A B : Ty Empty} {X : Paper.TypeCategory Empty}
    (l : obj A ⟶ X) (r : obj B ⟶ X) :
    (sumCofan A B).inl ≫ table l r = l := by
  rw [table, ← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]

private theorem table_right {A B : Ty Empty} {X : Paper.TypeCategory Empty}
    (l : obj A ⟶ X) (r : obj B ⟶ X) :
    (sumCofan A B).inr ≫ table l r = r := by
  rw [table, ← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]

private theorem embedding_targetStep (q : Bool → Option (Option Bool))
    (extra : obj U ⟶ obj U ⨿ obj D) :
    embedding ≫ targetStep q extra = table (targetOutput (q false)) (targetOutput (q true)) := by
  rw [show embedding = (sumCofan S U).inl from (sumCofan_inl S U).symm]
  exact table_left _ _

theorem reflect_square (p : Bool → Option Bool) (q : Bool → Option (Option Bool))
    (extra : obj U ⟶ obj U ⨿ obj D)
    (comm : projection.map (sourceStep p ≫ coprod.map (𝟙 (obj U)) embedding) =
      projection.map (embedding ≫ targetStep q extra)) :
    sourceStep p ≫ coprod.map (𝟙 (obj U)) embedding = embedding ≫ targetStep q extra := by
  rw [embedding_targetStep] at comm ⊢
  have left : (sumCofan (Φ := Empty) U U).inl ≫
      (sourceStep p ≫ coprod.map (𝟙 (obj U)) embedding) = targetOutput ((p false).map some) := by
    rw [← Category.assoc, sourceStep, table_left, sourceOutput_post]
  have right : (sumCofan (Φ := Empty) U U).inr ≫
      (sourceStep p ≫ coprod.map (𝟙 (obj U)) embedding) = targetOutput ((p true).map some) := by
    rw [← Category.assoc, sourceStep, table_right, sourceOutput_post]
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Φ := Empty) U U)
  · have h := congrArg (projection.map (sumCofan U U).inl ≫ ·) comm
    rw [← projection.map_comp, ← projection.map_comp, left, table_left] at h
    rw [left, table_left, targetOutput_injective h]
  · have h := congrArg (projection.map (sumCofan U U).inr ≫ ·) comm
    rw [← projection.map_comp, ← projection.map_comp, right, table_right] at h
    rw [right, table_right, targetOutput_injective h]

private theorem project_update :
    projection.map (boundReturn update_normalizes.typed.1) = projection.map embedding :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (Paper.RetainedLet.returnOnce_typed update_normalizes.typed.1)
    (.br (ℓ := 0) rfl update_normalizes.typed.2)).mpr
    (returnOnce_eq_branch update_normalizes)

private theorem project_map_update :
    projection.map (coprod.map (𝟙 (obj U)) (boundReturn update_normalizes.typed.1)) =
      projection.map (coprod.map (𝟙 (obj U)) embedding) :=
  Paper.Extension.Singleton.projection_map_coprod_map_congr Seed rfl project_update

theorem iterate_uniformity (p : Bool → Option Bool) (q : Bool → Option (Option Bool))
    (extra : obj U ⟶ obj U ⨿ obj D)
    {f : obj S ⟶ obj U ⨿ obj S} {g : obj D ⟶ obj U ⨿ obj D}
    (hf : projection.map f = projection.map (sourceStep p))
    (hg : projection.map g = projection.map (targetStep q extra))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj U)) (boundReturn update_normalizes.typed.1)) =
      projection.map (boundReturn update_normalizes.typed.1 ≫ g)) :
    projection.map (iterate f) = projection.map (boundReturn update_normalizes.typed.1) ≫
      projection.map (iterate g) := by
  apply update_normalizes.iterate_map_uniformity (fun h => .inl h) constructorSequencing hf hg
  apply reflect_square
  simpa only [Functor.map_comp, hf, hg, project_map_update, project_update] using comm

theorem recur_then_exit :
    projection.map (iterate (sourceStep (fun b => if b then none else some true))) =
      projection.map (boundReturn update_normalizes.typed.1) ≫
        projection.map (iterate (targetStep (fun b => if b then none else some (some true))
          (targetOutput (some none)))) := by
  apply iterate_uniformity _ _ _ rfl rfl
  rw [projection.map_comp, projection.map_comp, project_update, project_map_update,
    ← projection.map_comp, ← projection.map_comp]
  apply congrArg projection.map
  rw [embedding_targetStep]
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit (Φ := Empty) U U)
  · rw [← Category.assoc, sourceStep, table_left, sourceOutput_post, table_left]
    rfl
  · rw [← Category.assoc, sourceStep, table_right, sourceOutput_post, table_right]
    rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.FiniteSquare
