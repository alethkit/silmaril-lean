module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

public section

set_option backward.isDefEq.respectTransparency false

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open LetIter.Semantics.Categorical (TypeModel InstructionModel case_postcomp case_return_map)
open LetIter.ProofRelevant.Semantics.Categorical (caseWithContext extend duplicate)
open LambdaSSA.Semantics.Categorical
open SingletonDispatcher (labelHom_ext labelInject_payload payload_labelInject)
open Morphism.CaseSSA (erase_hasType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V) {A B : τ}

@[reassoc] private theorem labelInject_zero_pack :
    labelInject M (L := [A, B]) 0 (A := A) rfl ≫ pack M A B =
      coprod.inl ≫ (M.coprodIso A B).inv := by
  simp [labelInject, pack, labelObj]

@[reassoc] private theorem labelInject_one_pack :
    labelInject M (L := [A, B]) 1 (A := B) rfl ≫ pack M A B =
      coprod.inr ≫ (M.coprodIso A B).inv := by
  simp [labelInject, pack, labelObj]
  change eqToHom (rfl : M.obj B = M.obj B) ≫ _ = _
  simp only [eqToHom_refl, Category.id_comp]

private theorem pack_unpack :
    pack M A B ≫ unpack M A B = 𝟙 _ := by
  apply labelHom_ext M
  intro i X hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    simp only [labelInject_zero_pack_assoc, unpack, Iso.inv_hom_id_assoc,
      coprod.inl_desc, Category.comp_id]
  | succ i =>
    cases i with
    | zero =>
      cases Option.some.inj hi
      change labelInject M (L := [A, B]) 1 (A := B) rfl ≫ _ = _
      simp only [labelInject_one_pack_assoc, unpack, Iso.inv_hom_id_assoc,
        coprod.inr_desc, Category.comp_id]
    | succ i => simp [At] at hi

private theorem unpack_pack :
    unpack M A B ≫ pack M A B = 𝟙 _ := by
  apply (cancel_epi (M.coprodIso A B).inv).mp
  simp only [unpack, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, labelInject_zero_pack]
  · rw [coprod.inr_desc_assoc, labelInject_one_pack]

theorem packExit_unpackExit_proof : packExit M A B ≫ unpackExit M A B = 𝟙 _ := by
  rw [packExit, unpackExit, Category.assoc, ← Category.assoc (labelInject M 0 rfl),
    labelInject_payload, Category.id_comp, pack_unpack]

theorem unpackExit_packExit_proof : unpackExit M A B ≫ packExit M A B = 𝟙 _ := by
  simp only [unpackExit, packExit, Category.assoc, ← Category.assoc (unpack M A B),
    unpack_pack, Category.id_comp, payload_labelInject]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] [InstructionModel J M Φ]

private theorem decoder_denotes (Γ : VCtx τ) :
    RegionDenotes J M (decoder_hasType (Φ := Φ) (A := A) (B := B) Γ)
      (J.map (snd (ctxObj M Γ) (M.obj (coprod A B)) ≫ unpack M A B)) := by
  let left := labelInject M (L := [A, B]) 0 (A := A) rfl
  let right := labelInject M (L := [A, B]) 1 (A := B) rfl
  have d := RegionDenotes.case
    (Denotes.var (J := J) (M := M) (Φ := Φ) (Γ := coprod A B :: Γ) (i := 0) rfl)
    (RegionDenotes.br (h := (rfl : At [A, B] 0 A))
      (Denotes.var (i := 0) (Γ := A :: coprod A B :: Γ) rfl))
    (RegionDenotes.br (h := (rfl : At [A, B] 1 B))
      (Denotes.var (i := 0) (Γ := B :: coprod A B :: Γ) rfl))
  change RegionDenotes J M _ (caseWithContext J
    (J.map (snd (ctxObj M Γ) _) ≫ J.map (M.coprodIso A B).hom)
    (J.map (snd (ctxObj M (coprod A B :: Γ)) _) ≫ J.map left)
    (J.map (snd (ctxObj M (coprod A B :: Γ)) _) ≫ J.map right)) at d
  rw [← J.map_comp (snd _ _) left, ← J.map_comp (snd _ _) right, case_return_map,
    ← J.map_comp, ← J.map_comp, Category.assoc] at d
  exact d

variable [RegionTypingCoherent (Φ := Φ) J M]

theorem denote_decode_proof {n : Nat} {β : BoundCtx τ n} (c : Code Φ β (coprod A B)) :
    denoteRegion J M ((decode c).toSSA_hasType) =
      denoteRegion J M (c.toSSA_hasType (L := [coprod A B]) (exit := 0) rfl) ≫
        J.map (unpackExit M A B) := by
  let D := coprod A B
  let k := unpackExit M A B
  have hk : ContinuationDenotes J M (Γ := β.toList) (L := [D]) (fun _ => (decoder : Region Φ))
      (J.map (snd (ctxObj M β.toList) (labelObj M [D]) ≫ k)) := by
    intro i X h
    cases i with
    | zero =>
      cases Option.some.inj h
      rw [MonoidalCategory.id_tensorHom, ← J.map_comp, whiskerLeft_snd_assoc,
        show labelInject M 0 h ≫ k = unpack M A B by
          change labelInject M (L := [coprod A B]) 0 rfl ≫ unpackExit M A B = _
          rw [unpackExit, ← Category.assoc, labelInject_payload, Category.id_comp]]
      exact ⟨decoder_hasType _, decoder_denotes M J _⟩
    | succ i => simp [At] at h
  rw [denoteRegion_linkExits J M (c.toSSA_hasType (L := [D]) (exit := 0) rfl)
    (decode c).toSSA_hasType hk]
  set f := denoteRegion J M (c.toSSA_hasType (L := [D]) (exit := 0) rfl)
  have project : extend J f ≫ J.map (snd (ctxObj M β.toList) (labelObj M [D])) = f := by
    simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
      Category.id_comp, Category.assoc]
    rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
    simp [duplicate]
  simp only [LetIter.ProofRelevant.Semantics.Categorical.bind, J.map_comp,
    ← Category.assoc, project, k]

theorem denote_encode_proof {n : Nat} {β : BoundCtx τ n} (c : TwoExit Φ A B β) :
    denoteRegion J M (c.encode.toSSA_hasType (L := [coprod A B]) (exit := 0) rfl) =
      denoteRegion J M c.toSSA_hasType ≫ J.map (packExit M A B) := by
  induction c with
  | left a =>
    let da := denote_spec J M (erase_hasType a.2.toHasType)
    rw [← (RegionDenotes.br (h := (rfl : At [coprod A B] 0 (coprod A B)))
        (Denotes.inl (B := B) da)).eq_denote J M,
      ← (RegionDenotes.br (h := (rfl : At [A, B] 0 A)) da).eq_denote J M]
    simp only [Category.assoc, ← J.map_comp, packExit, labelInject_zero_pack_assoc]
  | right b =>
    let db := denote_spec J M (erase_hasType b.2.toHasType)
    rw [← (RegionDenotes.br (h := (rfl : At [coprod A B] 0 (coprod A B)))
        (Denotes.inr (A := A) db)).eq_denote J M,
      ← (RegionDenotes.br (h := (rfl : At [A, B] 1 B)) db).eq_denote J M]
    simp only [Category.assoc, ← J.map_comp, packExit, labelInject_one_pack_assoc]
  | case e l r ihl ihr =>
    let de := denote_spec J M (erase_hasType e.2.toHasType)
    rw [← (RegionDenotes.case de (denoteRegion_spec J M _) (denoteRegion_spec J M _)).eq_denote J M]
    rw [← (RegionDenotes.case de (denoteRegion_spec J M l.toSSA_hasType)
      (denoteRegion_spec J M r.toSSA_hasType)).eq_denote J M,
      case_postcomp, ← ihl, ← ihr]
  | dispatch c =>
    change denoteRegion J M (c.toSSA_hasType (L := [coprod A B]) (exit := 0) rfl) = _
    rw [denote_decode_proof M J c, Category.assoc, ← J.map_comp, unpackExit_packExit_proof,
      J.map_id, Category.comp_id]

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
