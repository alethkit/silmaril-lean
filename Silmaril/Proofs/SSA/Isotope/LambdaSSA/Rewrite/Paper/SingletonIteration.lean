module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Naturality.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

/-! # Iteration equations on paper singleton arrows -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open ContinuationContext (single)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B C : τ}

set_option backward.isDefEq.respectTransparency false

private def fromCfgEtaSingleton : CfgEta.TypeCategory Φ ([] : VCtx τ) ⥤ TypeCategory (τ := τ) Φ where
  obj A := ofType (show τ from A)
  map f := InducedCategory.homMk (Paper.fromCfgEta.map f.hom)
  map_id X := InducedCategory.hom_ext (Paper.fromCfgEta.map_id
    (show CfgEta.Interface Φ [] from CfgEta.fromNative.obj (single (show τ from X))))
  map_comp f g := InducedCategory.hom_ext (Paper.fromCfgEta.map_comp f.hom g.hom)

private theorem iterateSum_ofCfgEta
    (f : CfgEta.TypeCategory.ofType (Φ := Φ) (Γ := []) A ⟶
        CfgEta.TypeCategory.ofType (Γ := ([] : VCtx τ)) (Silmaril.coprod B A)) :
    iterateSum (A := A) (B := B) (fromCfgEtaSingleton.map f) =
      fromCfgEtaSingleton.map (CfgEta.TypeCategory.iterateSum (A := A) (B := B) f) := by
  apply InducedCategory.hom_ext
  change feedback (X := single A) (Y := single B)
    (Paper.fromCfgEta.map f.hom ≫ Paper.fromNative.map (SyntacticCategory.iterationDispatchHom A B)) =
    Paper.fromCfgEta.map (CfgEta.feedback (X := single A) (Y := single B)
      (f.hom ≫ CfgEta.fromNative.map (SyntacticCategory.iterationDispatchHom A B)))
  rw [← feedback_fromCfgEta, Functor.map_comp]
  rfl

private theorem map_ofRegion {p : Region Φ} (hp : ValueBranches [A] p [B]) :
    fromCfgEtaSingleton.map (CfgEta.TypeCategory.ofRegion hp) = ofRegion hp := rfl

theorem iterateSum_ofRegion {p : Region Φ} (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    iterateSum (ofRegion hp) = ofRegion (SyntacticCategory.iterateRegion_valueBranches hp) := by
  rw [← map_ofRegion hp, iterateSum_ofCfgEta, CfgEta.TypeCategory.iterateSum_ofRegion, map_ofRegion]

theorem coprod_desc_ofRegion {p q : Region Φ} (hp : ValueBranches [A] p [C])
    (hq : ValueBranches [B] q [C]) :
    (sumIso A B).hom ≫ coprod.desc (ofRegion hp) (ofRegion hq) =
      ofRegion (CfgEta.TypeCategory.caseValueBranches hp hq) := by
  let F : CfgEta.TypeCategory Φ ([] : VCtx τ) ⥤ TypeCategory (τ := τ) Φ := fromCfgEtaSingleton
  let e := CfgEta.TypeCategory.sumIso (Φ := Φ) (Γ := []) A B
  let cap := coprod.desc (CfgEta.TypeCategory.ofRegion hp) (CfgEta.TypeCategory.ofRegion hq)
  have eq := CfgEta.TypeCategory.coprod_desc_ofRegion hp hq
  have h := congrArg F.map eq
  change F.map (e.hom ≫ cap) = ofRegion (CfgEta.TypeCategory.caseValueBranches hp hq) at h
  rw [← h]
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A B)
  · simp only [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]
    change ofRegion hp = F.map (CfgEta.TypeCategory.sumCofan A B).inl ≫ F.map (e.hom ≫ cap)
    rw [← F.map_comp, ← Category.assoc]
    dsimp only [e, cap]
    rw [CfgEta.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc]
    rfl
  · simp only [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]
    change ofRegion hq = F.map (CfgEta.TypeCategory.sumCofan A B).inr ≫ F.map (e.hom ≫ cap)
    rw [← F.map_comp, ← Category.assoc]
    dsimp only [e, cap]
    rw [CfgEta.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc]
    rfl

theorem iterate_fixpoint {X Y : TypeCategory (τ := τ) Φ} (f : X ⟶ Y ⨿ X) :
    Paper.TypeCategory.iterate f = f ≫ coprod.desc (𝟙 Y) (Paper.TypeCategory.iterate f) := by
  let A : τ := X
  let B : τ := Y
  let e := sumIso (Φ := Φ) B A
  obtain ⟨p, hp, h⟩ := exists_ofRegion (A := A) (B := Silmaril.coprod B A) (f ≫ e.inv)
  have hf : ofRegion hp ≫ e.hom = f := by
    rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hiter : Paper.TypeCategory.iterate f =
      ofRegion (SyntacticCategory.iterateRegion_valueBranches hp) := by
    change iterateSum (A := A) (B := B) (f ≫ e.inv) = _
    rw [h, iterateSum_ofRegion]
  rw [hiter, ← hf, Category.assoc]
  dsimp only [e]
  have hid : ofRegion (r := (.br 0 (.var 0) : Region Φ))
      (show ValueBranches [B] (.br 0 (.var 0)) [B] from .br rfl (.var rfl)) = 𝟙 (ofType B) := by
    exact (congrArg fromCfgEtaSingleton.map (CfgEta.TypeCategory.ofRegion_identity (Φ := Φ) (Γ := []) B)).trans
      (fromCfgEtaSingleton.map_id _)
  rw [← hid, coprod_desc_ofRegion]
  -- The two weakenings of the case arms give the typed return-or-repeat decoder.
  have uv : ValueBranches [A] (compLSubst (fun _ => p)
      (fun _ => .case (.var 0) ((Region.br 0 (.var 0)).renameVars (Silmaril.DeBruijn.lift Nat.succ))
        ((SyntacticCategory.iterateRegion A p).renameVars (Silmaril.DeBruijn.lift Nat.succ))) 0) [B] := by
    change ValueBranches [A] (p.lsubst (fun _ =>
      (Region.case (.var 0) ((Region.br 0 (.var 0)).renameVars (Silmaril.DeBruijn.lift Nat.succ))
        ((SyntacticCategory.iterateRegion A p).renameVars (Silmaril.DeBruijn.lift Nat.succ))).renameVars
          (Silmaril.DeBruijn.lift Nat.succ))) [B]
    rw [CfgEta.TypeCategory.returnOrRepeat_lift]
    exact CfgEta.TypeCategory.unrolled_valueBranches hp
  rw [ofRegion_comp hp _ uv, ofRegion_eq_iff]
  change Paper.Eqv [A] (SyntacticCategory.iterateRegion A p)
    (p.lsubst (fun _ =>
      (Region.case (.var 0) ((Region.br 0 (.var 0)).renameVars (Silmaril.DeBruijn.lift Nat.succ))
        ((SyntacticCategory.iterateRegion A p).renameVars (Silmaril.DeBruijn.lift Nat.succ))).renameVars
          (Silmaril.DeBruijn.lift Nat.succ))) [B]
  rw [CfgEta.TypeCategory.returnOrRepeat_lift]
  exact Paper.fixpoint hp

@[reassoc]
theorem inl_iterationDispatchArrow (A B : TypeCategory (τ := τ) Φ) :
    (toInterface Φ).map (coprod.inl : B ⟶ B ⨿ A) ≫ iterationDispatchArrow A B =
      Paper.fromNative.map ((single (show τ from A)).appendInr (single (show τ from B))) := by
  let a : τ := A
  let b : τ := B
  have h : (coprod.inl : B ⟶ B ⨿ A) ≫ (sumIso b a).inv = (sumCofan b a).inl := by
    rw [← sumCofan_inl_sumIso_hom b a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e := congrArg (Paper.fromCfgEta (Φ := Φ) (Γ := [])).map
    (CfgEta.TypeCategory.iterationDispatch_inl (Φ := Φ) (Γ := []) a b)
  rw [Functor.map_comp] at e
  change (coprod.inl : B ⟶ B ⨿ A).hom ≫ (sumIso b a).inv.hom ≫ _ = _
  rw [← Category.assoc]
  change ((coprod.inl : B ⟶ B ⨿ A) ≫ (sumIso b a).inv).hom ≫ _ = _
  rw [h]
  exact e

@[reassoc]
theorem inr_iterationDispatchArrow (A B : TypeCategory (τ := τ) Φ) :
    (toInterface Φ).map (coprod.inr : A ⟶ B ⨿ A) ≫ iterationDispatchArrow A B =
      Paper.fromNative.map ((single (show τ from A)).appendInl (single (show τ from B))) := by
  let a : τ := A
  let b : τ := B
  have h : (coprod.inr : A ⟶ B ⨿ A) ≫ (sumIso b a).inv = (sumCofan b a).inr := by
    rw [← sumCofan_inr_sumIso_hom b a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e := congrArg (Paper.fromCfgEta (Φ := Φ) (Γ := [])).map
    (CfgEta.TypeCategory.iterationDispatch_inr (Φ := Φ) (Γ := []) a b)
  rw [Functor.map_comp] at e
  change (coprod.inr : A ⟶ B ⨿ A).hom ≫ (sumIso b a).inv.hom ≫ _ = _
  rw [← Category.assoc]
  change ((coprod.inr : A ⟶ B ⨿ A) ≫ (sumIso b a).inv).hom ≫ _ = _
  rw [h]
  exact e

theorem toInterface_map_iterate {A B : TypeCategory (τ := τ) Φ} (f : A ⟶ B ⨿ A) :
    (toInterface Φ).map (Paper.TypeCategory.iterate f) =
      feedback (X := single (show τ from A)) (Y := single (show τ from B))
        ((toInterface Φ).map f ≫ iterationDispatchArrow A B) := by
  unfold Paper.TypeCategory.iterate iterateSum iterationDispatchArrow
  change feedback (X := single (show τ from A)) (Y := single (show τ from B))
    ((f.hom ≫ (sumIso (show τ from B) (show τ from A)).inv.hom) ≫ _) = _
  rw [Category.assoc]
  rfl

theorem chosen_sum_hom_ext {A B : TypeCategory (τ := τ) Φ} {Z : Interface Φ ([] : VCtx τ)}
    {p q : (toInterface Φ).obj (B ⨿ A) ⟶ Z}
    (hl : (toInterface Φ).map (coprod.inl : B ⟶ B ⨿ A) ≫ p = (toInterface Φ).map coprod.inl ≫ q)
    (hr : (toInterface Φ).map (coprod.inr : A ⟶ B ⨿ A) ≫ p = (toInterface Φ).map coprod.inr ≫ q) :
    p = q := by
  let a : τ := A
  let b : τ := B
  let F : TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) := toInterface Φ
  let e := F.mapIso (sumIso b a)
  apply (cancel_epi e.hom).mp
  apply BinaryCofan.IsColimit.hom_ext (singletonSumIsColimit (Φ := Φ) (Γ := []) b a)
  · change F.map (sumCofan b a).inl ≫ F.map (sumIso b a).hom ≫ p =
      F.map (sumCofan b a).inl ≫ F.map (sumIso b a).hom ≫ q
    simpa only [← Category.assoc, ← F.map_comp, sumCofan_inl_sumIso_hom] using hl
  · change F.map (sumCofan b a).inr ≫ F.map (sumIso b a).hom ≫ p =
      F.map (sumCofan b a).inr ≫ F.map (sumIso b a).hom ≫ q
    simpa only [← Category.assoc, ← F.map_comp, sumCofan_inr_sumIso_hom] using hr

theorem iterate_naturality {A B C : TypeCategory (τ := τ) Φ} (f : A ⟶ B ⨿ A) (g : B ⟶ C) :
    Paper.TypeCategory.iterate f ≫ g = Paper.TypeCategory.iterate (f ≫ coprod.map g (𝟙 A)) := by
  let F : TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) := toInterface Φ
  have h : F.map (coprod.map g (𝟙 A)) ≫ iterationDispatchArrow A C =
      iterationDispatchArrow A B ≫ prepend (single (show τ from A)) (F.map g) := by
    apply chosen_sum_hom_ext
    · change F.map (coprod.inl : B ⟶ B ⨿ A) ≫ _ = _
      rw [← F.map_comp_assoc, coprod.inl_map, F.map_comp, Category.assoc,
        inl_iterationDispatchArrow, inl_iterationDispatchArrow_assoc, appendInr_prepend]
      rfl
    · change F.map (coprod.inr : A ⟶ B ⨿ A) ≫ _ = _
      rw [← F.map_comp_assoc, coprod.inr_map, Category.id_comp,
        inr_iterationDispatchArrow, inr_iterationDispatchArrow_assoc, appendInl_prepend]
      rfl
  apply F.map_injective
  rw [F.map_comp, toInterface_map_iterate, feedback_postcompose, toInterface_map_iterate, F.map_comp]
  simp only [Category.assoc, h]
  rfl

-- Test the two outer injections to identify duplicate-label collapse.
private theorem nested_dispatch (A B : TypeCategory (τ := τ) Φ) :
    iterationDispatchArrow A (B ⨿ A) ≫
        prepend (single (show τ from A)) (iterationDispatchArrow A B) ≫ collapseLabels (show τ from A) (single (show τ from B)) =
      (toInterface Φ).map (coprod.desc (𝟙 (B ⨿ A)) coprod.inr) ≫ iterationDispatchArrow A B := by
  let F : TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) := toInterface Φ
  apply chosen_sum_hom_ext
  · change F.map (coprod.inl : (B ⨿ A) ⟶ (B ⨿ A) ⨿ A) ≫ _ = _
    rw [inl_iterationDispatchArrow_assoc, appendInr_prepend_assoc, collapseLabels_right, Category.comp_id,
      ← F.map_comp_assoc, coprod.inl_desc, F.map_id, Category.id_comp]
  · change F.map (coprod.inr : A ⟶ (B ⨿ A) ⨿ A) ≫ _ = _
    rw [inr_iterationDispatchArrow_assoc, appendInl_prepend_assoc, collapseLabels_left,
      ← F.map_comp_assoc, coprod.inr_desc, inr_iterationDispatchArrow]

theorem iterate_codiagonal {A B : TypeCategory (τ := τ) Φ} (f : A ⟶ (B ⨿ A) ⨿ A) :
    Paper.TypeCategory.iterate (Paper.TypeCategory.iterate f) =
      Paper.TypeCategory.iterate (f ≫ coprod.desc (𝟙 (B ⨿ A)) coprod.inr) := by
  let F : TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) := toInterface Φ
  apply F.map_injective
  rw [toInterface_map_iterate, toInterface_map_iterate, feedback_postcompose, feedback_codiagonal, toInterface_map_iterate, F.map_comp]
  simp only [Category.assoc, nested_dispatch]
  rfl

private theorem simulation_dispatch {A D B : τ} {a : Tm Φ} (ha : Tm.BranchValue [A] a D) :
    let F : TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) := toInterface Φ
    let h := ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha)
    F.map (coprod.map (𝟙 (ofType B)) h) ≫ iterationDispatchArrow (ofType D) (ofType B) =
      iterationDispatchArrow (ofType A) (ofType B) ≫ localStateChange (single B) ha := by
  dsimp only
  let F : TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) := toInterface Φ
  apply chosen_sum_hom_ext
  · change F.map (coprod.inl : ofType B ⟶ ofType B ⨿ ofType A) ≫ _ = _
    rw [← F.map_comp_assoc, coprod.inl_map, Category.id_comp, inl_iterationDispatchArrow, inl_iterationDispatchArrow_assoc,
      localStateChange_right]
  · change F.map (coprod.inr : ofType A ⟶ ofType B ⨿ ofType A) ≫ _ = _
    rw [← F.map_comp_assoc, coprod.inr_map, F.map_comp, Category.assoc,
      inr_iterationDispatchArrow, inr_iterationDispatchArrow_assoc, localStateChange_left]
    rfl

theorem iterate_uniformity_ofBranchValue {A D B : τ} {a : Tm Φ} (ha : Tm.BranchValue [A] a D)
    (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (g : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D)
    (comm : f ≫ coprod.map (𝟙 (ofType B)) (ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha)) =
      ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha) ≫ g) :
    Paper.TypeCategory.iterate f =
      ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha) ≫ Paper.TypeCategory.iterate g := by
  let F : TypeCategory (τ := τ) Φ ⥤ Interface Φ ([] : VCtx τ) := toInterface Φ
  let h := ofRegion (r := .br 0 a) (.br (ℓ := 0) rfl ha)
  have square : (F.map f ≫ iterationDispatchArrow (ofType A) (ofType B)) ≫ localStateChange (single B) ha =
      stateChange ha ≫ (F.map g ≫ iterationDispatchArrow (ofType D) (ofType B)) := by
    change (F.map f ≫ iterationDispatchArrow (ofType A) (ofType B)) ≫ _ =
      F.map h ≫ (F.map g ≫ iterationDispatchArrow (ofType D) (ofType B))
    rw [Category.assoc, ← simulation_dispatch (B := B) ha, ← F.map_comp_assoc, comm, F.map_comp,
      Category.assoc]
  apply F.map_injective
  change F.map (Paper.TypeCategory.iterate f) = F.map (h ≫ Paper.TypeCategory.iterate g)
  rw [F.map_comp, toInterface_map_iterate, toInterface_map_iterate]
  exact feedback_uniformity (single B) ha _ _ square

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonIteration
