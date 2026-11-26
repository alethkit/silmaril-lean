module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms

public section

set_option backward.isDefEq.respectTransparency false

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Region (packedExitType)
open LetIter.Semantics.Categorical (TypeModel InstructionModel case_postcomp case_return_map)
open LetIter.ProofRelevant.Semantics.Categorical (caseWithContext extend duplicate)
open CategoryTheory.CartesianMonoidalCategory (snd)
open LambdaSSA.Semantics.Categorical
open SingletonDispatcher (labelInject_payload)
open Morphism.CaseSSA (erase erase_hasType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

omit [FreydCategory.CentralUnit J] [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] in
private theorem tag_denotes [DistributiveFreydCategory J]
    {n : Nat} {β : BoundCtx τ n} {L : LCtx τ} {i : Nat} {A : τ}
    (hi : At L i A) (a : Operand Φ β A)
    {f : J.obj (ctxObj M β.toList) ⟶ J.obj (M.obj A)}
    (d : Denotes J M (erase_hasType a.2.toHasType) f) :
    Denotes J M (erase_hasType (tag L i hi a).2.toHasType)
      (f ≫ J.map (packedLabelInject M i hi)) := by
  induction L generalizing i with
  | nil => simp [At] at hi
  | cons B L ih =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      simpa only [packedLabelInject, eqToHom_refl, Category.id_comp] using
        (Denotes.inl (B := packedExitType L) d)
    | succ i =>
      simpa only [packedLabelInject, J.map_comp, Category.assoc] using
        (Denotes.inr (A := B) (ih (show At L i A from hi)))

variable [RegionTypingCoherent (Φ := Φ) J M]

theorem denote_linkSingleton_proof {Γ : VCtx τ} {L : LCtx τ} {A : τ}
    {r s : Region Φ} (hr : Region.HasType Γ r [A]) (hs : Region.HasType (A :: Γ) s L)
    (hlink : Region.HasType Γ (r.linkExits [A] (fun _ => s)) L) :
    denoteRegion J M hlink = LetIter.ProofRelevant.Semantics.Categorical.bind J (denoteRegion J M hr)
      (J.map (ctxObj M Γ ◁ singletonLabelPayload M A) ≫ denoteRegion J M hs) := by
  apply denoteRegion_linkExits J M hr hlink
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    refine ⟨hs, ?_⟩
    rw [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      labelInject_payload, MonoidalCategory.whiskerLeft_id]
    change RegionDenotes J M hs (J.map (𝟙 (ctxObj M (A :: Γ))) ≫ denoteRegion J M hs)
    rw [J.map_id, Category.id_comp]
    exact denoteRegion_spec J M hs
  | succ i => simp [At] at hi

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem same_region {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : r = s)
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  cases e
  rfl

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
theorem denote_toFinite_proof {A B : τ} {n : Nat} {β : BoundCtx τ n} (c : TwoExit Φ A B β) :
    denoteRegion J M c.toFinite.toSSA_hasType = denoteRegion J M c.toSSA_hasType :=
  same_region J M c.toSSA_toFinite _ _

theorem denote_encode_proof {L : LCtx τ} {n : Nat} {β : BoundCtx τ n}
    (c : FiniteExit Φ L β) :
    denoteRegion J M (c.encode.toSSA_hasType (L := [packedExitType L]) (exit := 0) rfl) =
      denoteRegion J M c.toSSA_hasType ≫ J.map (packLabelExit M L) := by
  induction c with
  | br hi a =>
    let d := denote_spec J M (erase_hasType a.2.toHasType)
    rw [← (RegionDenotes.br (h := (rfl : At [packedExitType L] 0 (packedExitType L)))
        (tag_denotes J M hi a d)).eq_denote J M,
      ← (RegionDenotes.br (h := hi) d).eq_denote J M]
    simp only [Category.assoc, ← J.map_comp, packLabelExit, labelInject_packLabel_assoc]
  | case e l r ihl ihr =>
    let de := denote_spec J M (erase_hasType e.2.toHasType)
    rw [← (RegionDenotes.case de (denoteRegion_spec J M _) (denoteRegion_spec J M _)).eq_denote J M]
    rw [← (RegionDenotes.case de (denoteRegion_spec J M l.toSSA_hasType)
      (denoteRegion_spec J M r.toSSA_hasType)).eq_denote J M, case_postcomp, ← ihl, ← ihr]
  | @join n β A a b ih =>
    let ha := a.toSSA_hasType (L := [A]) (exit := 0) rfl
    let hb := b.encode.toSSA_hasType (L := [packedExitType L]) (exit := 0) rfl
    have hp : Region.HasType β.toList
        ((a.toSSA 0).linkExits [A] (fun _ => b.encode.toSSA 0)) [packedExitType L] := by
      apply ha.linkExits
      intro i B hi
      cases i with
      | zero => cases Option.some.inj hi; exact hb
      | succ i => simp [At] at hi
    have e : (Code.join a b.encode).toSSA 0 =
        (a.toSSA 0).linkExits [A] (fun _ => b.encode.toSSA 0) := by
      simp [Code.toSSA, Region.linkExits, Code.toSSA_renameLabels]
    change denoteRegion J M ((Code.join a b.encode).toSSA_hasType
      (L := [packedExitType L]) (exit := 0) rfl) = _
    rw [same_region J M e _ hp, denote_linkSingleton_proof J M ha hb hp,
      denote_linkSingleton_proof J M ha b.toSSA_hasType (FiniteExit.join a b).toSSA_hasType, ih]
    simp only [LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]

omit [RegionTypingCoherent (Φ := Φ) J M] in
private theorem decodeBody_denotes {K : LCtx τ} {j : Nat} {D : τ} (fallback : At K j D)
    (L : LCtx τ) {ρ : Nat → Nat} (ren : Ren L K ρ) {n : Nat} (β : BoundCtx τ n) :
    RegionDenotes J M (decodeBody (Φ := Φ) fallback L ren β).toSSA_hasType
      (J.map (snd (ctxObj M β.toList) (M.obj (packedExitType L)) ≫
        unpackLabel M L ≫ labelMap M ren)) := by
  induction L generalizing ρ n with
  | nil =>
    have d := RegionDenotes.br (h := fallback) (Denotes.abort
      (Denotes.var (J := J) (M := M) (Φ := Φ)
        (Γ := (Silmaril.empty : τ) :: β.toList) (i := 0) rfl))
    have out : M.emptyIsInitial.to (M.obj D) ≫ labelInject M j fallback =
        unpackLabel M [] ≫ labelMap M ren :=
      M.emptyIsInitial.hom_ext _ _
    change RegionDenotes J M (decodeBody (Φ := Φ) fallback [] ren β).toSSA_hasType
      ((J.map (snd (ctxObj M β.toList) (M.obj (Silmaril.empty : τ))) ≫
      J.map (M.emptyIsInitial.to (M.obj D))) ≫ J.map (labelInject M j fallback)) at d
    rw [Category.assoc, ← J.map_comp, out, ← J.map_comp] at d
    exact d
  | cons A L ih =>
    let T := packedExitType (A :: L)
    let E := ctxObj M (T :: β.toList)
    let tailRen := SSA.Ren.comp (SSA.Ren.wk L A) ren
    let leftArrow := labelInject M (ρ 0) (ren (rfl : At (A :: L) 0 A))
    let rightArrow := unpackLabel M L ≫ labelMap M tailRen
    have dl := RegionDenotes.br (h := ren (rfl : At (A :: L) 0 A))
      (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (Γ := A :: T :: β.toList) rfl)
    have dr := ih tailRen (β.snoc T)
    have d := RegionDenotes.case
      (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (Γ := T :: β.toList) rfl) dl dr
    change RegionDenotes J M _
      (caseWithContext J (J.map (snd (ctxObj M β.toList) (M.obj T)) ≫
        J.map (M.coprodIso A (packedExitType L)).hom)
        (J.map (snd E (M.obj A)) ≫ J.map leftArrow)
        (J.map (snd E (M.obj (packedExitType L)) ≫ rightArrow))) at d
    rw [← J.map_comp (snd E (M.obj A)) leftArrow, case_return_map] at d
    have out : coprod.desc leftArrow rightArrow =
        coprod.desc (labelInject M (L := A :: L) 0 rfl)
          (unpackLabel M L ≫ labelMap M (SSA.Ren.wk L A)) ≫ labelMap M ren := by
      apply coprod.hom_ext
      · simp only [coprod.inl_desc, coprod.inl_desc_assoc, labelInject_labelMap, leftArrow]
      · simp only [coprod.inr_desc, coprod.inr_desc_assoc, rightArrow]
        rw [show labelMap M tailRen = _ from labelMap_comp M (SSA.Ren.wk L A) ren, Category.assoc]
    rw [out, ← J.map_comp, ← J.map_comp, Category.assoc, ← Category.assoc (M.coprodIso A _).hom] at d
    exact d

theorem denote_decode_proof {n : Nat} {β : BoundCtx τ n} {L : LCtx τ} (hne : L ≠ [])
    (c : Code Φ β (packedExitType L)) :
    denoteRegion J M (decode hne c).toSSA_hasType =
      denoteRegion J M (c.toSSA_hasType (L := [packedExitType L]) (exit := 0) rfl) ≫
        J.map (unpackLabelExit M L) := by
  cases L with
  | nil => exact (hne rfl).elim
  | cons A L =>
    let T := packedExitType (A :: L)
    let body := decodeBody (Φ := Φ) (rfl : At (A :: L) 0 A) (A :: L) (SSA.Ren.id (A :: L)) β
    let entry := c.toSSA_hasType (L := [T]) (exit := 0) rfl
    have den := (decodeBody_denotes (Φ := Φ) J M (rfl : At (A :: L) 0 A)
      (A :: L) (SSA.Ren.id (A :: L)) β).eq_denote J M
    change J.map (snd (ctxObj M β.toList) (M.obj T) ≫
      unpackLabel M (A :: L) ≫ labelMap M (SSA.Ren.id (A :: L))) =
        denoteRegion J M body.toSSA_hasType at den
    rw [labelMap_id, Category.comp_id] at den
    rw [denote_linkSingleton_proof J M entry body.toSSA_hasType (decode hne c).toSSA_hasType, ← den]
    let f := denoteRegion J M entry
    have project : extend J f ≫ J.map (snd (ctxObj M β.toList) (labelObj M [T])) = f := by
      simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
        Category.id_comp, Category.assoc]
      rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
      simp [duplicate]
    change LetIter.ProofRelevant.Semantics.Categorical.bind J f _ = f ≫ _
    rw [← J.map_comp, CartesianMonoidalCategory.whiskerLeft_snd_assoc]
    simp only [LetIter.ProofRelevant.Semantics.Categorical.bind, J.map_comp,
      ← Category.assoc, project, unpackLabelExit, T]

end Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit
