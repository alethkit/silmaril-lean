module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Denotation of the guarded left action -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationWhisker

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

open Silmaril.Isotope.LambdaSSA.Region
open CfgEta.TypeCategory (whiskerLeftRegion whiskerLeftRegion_typed whiskerLeftBody productSndBranches)
open CfgEta.TypeCategory.ConstructorReification (sndMap)
open CartesianMonoidalCategory (fst snd lift)
open SingletonDispatcher (labelInject_payload denote_weakenCapture)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (extend_map pair_maps_eq_map_lift retainEnvironment bind_retainEnvironment
    retainEnvironment_pre_assoc retainEnvironment_comp retainEnvironment_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend retainLeft)
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

set_option backward.isDefEq.respectTransparency false in
private noncomputable def splitInput (X A : τ) :
    M.obj (product X A) ⟶ ctxObj M [A, X, product X A] :=
  let P := M.obj (product X A)
  let E := 𝟙_ V ⊗ P
  (λ_ P).inv ≫ lift (𝟙 E) (snd (𝟙_ V) P) ≫
    ((𝟙 E) ⊗ₘ (M.productIso X A).hom) ≫ (ctxPairIso M [product X A] X A).hom

omit [SymmetricCategory V] [DistributiveTensor V] in
set_option backward.isDefEq.respectTransparency false in
private theorem splitInput_active (X A : τ) :
    splitInput M X A ≫ lookup M 0 (rfl : At [A, X, product X A] 0 A) =
      (M.productIso X A).hom ≫ snd (M.obj X) (M.obj A) := by
  let E := 𝟙_ V ⊗ M.obj (product X A)
  have step : (ctxPairIso M [product X A] X A).hom ≫ snd (E ⊗ M.obj X) (M.obj A) =
      snd E (M.obj X ⊗ M.obj A) ≫ snd (M.obj X) (M.obj A) :=
    CartesianMonoidalCategory.associator_inv_snd E (M.obj X) (M.obj A)
  simp only [splitInput, lookup, ctxObj, Category.assoc]
  dsimp only [E] at step
  rw [step, CartesianMonoidalCategory.tensorHom_snd_assoc, CartesianMonoidalCategory.lift_snd_assoc,
    CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]

omit [SymmetricCategory V] [DistributiveTensor V] in
set_option backward.isDefEq.respectTransparency false in
private theorem splitInput_capture (X A : τ) :
    splitInput M X A ≫ lookup M 1 (rfl : At [A, X, product X A] 1 X) =
      (M.productIso X A).hom ≫ fst (M.obj X) (M.obj A) := by
  let E := 𝟙_ V ⊗ M.obj (product X A)
  have step : (ctxPairIso M [product X A] X A).hom ≫ fst (E ⊗ M.obj X) (M.obj A) ≫ snd E (M.obj X) =
      snd E (M.obj X ⊗ M.obj A) ≫ fst (M.obj X) (M.obj A) :=
    CartesianMonoidalCategory.associator_inv_fst_snd E (M.obj X) (M.obj A)
  simp only [splitInput, lookup, ctxObj, Category.assoc]
  dsimp only [E] at step
  rw [step, CartesianMonoidalCategory.tensorHom_snd_assoc, CartesianMonoidalCategory.lift_snd_assoc,
    CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]

omit [FreydCategory.CentralUnit J] in
set_option backward.isDefEq.respectTransparency false in
private theorem unpack_then {X A D : τ} {r : Region Φ}
    (hr : HasType [A, X, product X A] r [D]) :
    denoteSingletonRegion J M (.let₂ (.var (i := 0) rfl) hr :
      HasType [product X A] (.let₂ (.var 0) r) [D]) =
      J.map (splitInput M X A) ≫ denoteRegion J M hr ≫ J.map (singletonLabelPayload M D) := by
  have graph := RegionDenotes.let₂
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [product X A] 0 (product X A)))
    (denoteRegion_spec J M hr)
  rw [denoteSingletonRegion, ← graph.eq_denote J M]
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [extend_map]
  simp only [splitInput, lookup, ctxObj, J.map_comp, Category.assoc]

omit [FreydCategory.CentralUnit J] in
set_option backward.isDefEq.respectTransparency false in
theorem denoteSingleton_productSnd (A B : τ) :
    denoteSingletonRegion J M (productSndBranches (Φ := Φ) A B).hasType = J.map (sndMap M A B) := by
  let d := RegionDenotes.br (h := (rfl : At [B] 0 B))
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [B, A, product A B] 0 B))
  let h : HasType [B, A, product A B] (.br 0 (.var 0) : Region Φ) [B] := .br rfl (.var rfl)
  rw [unpack_then J M h, ← d.eq_denote (h := h) J M]
  simp only [Category.assoc, ← J.map_comp, labelInject_payload, Category.comp_id]
  rw [splitInput_active]
  rfl

omit [FreydCategory.CentralUnit J] in
set_option backward.isDefEq.respectTransparency false in
private theorem keep_capture {X A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    ∃ (h : ValueBranches [A, X, product X A]
        (r.renameVars (Silmaril.DeBruijn.lift (Nat.succ ∘ Nat.succ))) [B]),
      denoteRegion J M h.hasType =
        J.map (lookup M 0 (rfl : At [A, X, product X A] 0 A) ≫ (λ_ (M.obj A)).inv) ≫
          denoteRegion J M hr.hasType := by
  let hp := hr.renameVars ((Ren.wk ([] : VCtx τ) (product X A)).lift A)
  let hx := hp.renameVars ((Ren.wk [product X A] X).lift A)
  have shape :
      (r.renameVars (Silmaril.DeBruijn.lift Nat.succ)).renameVars (Silmaril.DeBruijn.lift Nat.succ) =
        r.renameVars (Silmaril.DeBruijn.lift (Nat.succ ∘ Nat.succ)) := by
    rw [Region.renameVars_comp]
    congr 1
    funext i
    cases i <;> rfl
  let ht : ValueBranches [A, X, product X A] _ [B] := shape ▸ hx
  refine ⟨ht, ?_⟩
  have congrDenote {r s : Region Φ} (e : r = s)
      (hr : HasType [A, X, product X A] r [B]) (hs : HasType [A, X, product X A] s [B]) :
      denoteRegion J M hr = denoteRegion J M hs := by cases e; rfl
  rw [congrDenote shape.symm ht.hasType hx.hasType]
  let hpType := hr.hasType.renameVars ((Ren.wk ([] : VCtx τ) (product X A)).lift A)
  change denoteRegion J M (hpType.renameVars ((Ren.wk [product X A] X).lift A)) = _
  rw [denote_weakenCapture M J hpType, denote_weakenCapture M J hr.hasType, ← J.map_comp_assoc]
  congr 2
  apply CartesianMonoidalCategory.hom_ext
  · change (_ : _ ⟶ 𝟙_ V) = _
    exact Subsingleton.elim _ _
  · change (_ ≫ _) ≫ snd (𝟙_ V) (M.obj A) = _
    simp only [Category.assoc, CartesianMonoidalCategory.whiskerRight_snd,
      CartesianMonoidalCategory.leftUnitor_inv_snd,
      Category.comp_id, lookup, ctxObj]

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
set_option backward.isDefEq.respectTransparency false in
private theorem continuationPair (X A B : τ) :
    ContinuationDenotes J M (Γ := [A, X, product X A]) (L := [B]) (K := [product X B])
      (fun _ => (.br 0 (.pair (.var 2) (.var 0)) : Region Φ))
      (J.map (lookup M 1 (rfl : At [A, X, product X A] 1 X) ▷ labelObj M [B]) ≫
        J.map (M.obj X ◁ singletonLabelPayload M B) ≫ J.map (M.productIso X B).inv ≫
        J.map (labelInject M 0 (rfl : At [product X B] 0 (product X B)))) := by
  intro i D hi
  have zero : i = 0 := by simpa using (List.getElem?_eq_some_iff.mp hi).1
  subst i
  cases Option.some.inj hi
  let E := ctxObj M [A, X, product X A]
  let p : E ⟶ M.obj X := lookup M 1 (rfl : At [A, X, product X A] 1 X)
  let i := labelInject M 0 (rfl : At [B] 0 B)
  let out := labelInject M 0 (rfl : At [product X B] 0 (product X B))
  let q := singletonLabelPayload M B
  let d := Denotes.pair
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 2) (rfl : At [B, A, X, product X A] 2 X))
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [B, A, X, product X A] 0 B))
  let h : HasType [B, A, X, product X A] (.br 0 (.pair (.var 2) (.var 0)) : Region Φ) [product X B] :=
    .br rfl (.pair (.var rfl) (.var rfl))
  refine ⟨h, ?_⟩
  have eq : ((𝟙 E) ⊗ₘ i) ≫ (p ▷ labelObj M [B]) ≫ (M.obj X ◁ q) =
      lift (fst E (M.obj B) ≫ p) (snd E (M.obj B)) := by
    rw [← MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.id_comp, show i ≫ q = 𝟙 _ from labelInject_payload M B]
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.tensorHom_fst, CartesianMonoidalCategory.lift_fst]
    · rw [CartesianMonoidalCategory.tensorHom_snd, CartesianMonoidalCategory.lift_snd, Category.comp_id]
  change RegionDenotes J M h (J.map ((𝟙 E) ⊗ₘ i) ≫
    J.map (p ▷ labelObj M [B]) ≫ J.map (M.obj X ◁ q) ≫ J.map (M.productIso X B).inv ≫ J.map out)
  rw [← J.map_comp_assoc, ← J.map_comp_assoc, Category.assoc, eq, ← Category.assoc (J.map (lift _ _)),
    ← pair_maps_eq_map_lift]
  exact .br d

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared in
set_option backward.isDefEq.respectTransparency false in
theorem denoteSingleton_whiskerLeft (X : τ) {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    denoteSingletonRegion J M (whiskerLeftRegion_typed X hr).hasType =
      J.map (M.productIso X A).hom ≫ retainLeft J (R := M.obj X)
        (denoteSingletonRegion J M hr.hasType) ≫ J.map (M.productIso X B).inv := by
  obtain ⟨h, eh⟩ := keep_capture J M (X := X) hr
  let body := CfgEta.TypeCategory.whiskerLeftBody_typed X hr
  change denoteSingletonRegion J M (.let₂ (.var (i := 0) rfl) body.hasType :
    HasType [product X A] (.let₂ (.var 0) (whiskerLeftBody r)) [product X B]) = _
  rw [unpack_then J M body.hasType]
  have calcBody := denoteRegion_lsubst_sharedTensor J M shared h.hasType body.hasType
    (PureBranches.of_valueBranches J M h) (continuationPair J M X A B)
  rw [calcBody, eh, bind_retainEnvironment J, Category.assoc, retainEnvironment_pre_assoc J,
    splitInput_capture, ← J.map_comp_assoc, Category.assoc, reassoc_of% (splitInput_active M X A)]
  let q := singletonLabelPayload M B
  have retain_q : retainLeft J (R := M.obj X) (J.map q) = J.map (M.obj X ◁ q) := by
    simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]
  have untag : J.map (labelInject M 0 (rfl : At [product X B] 0 (product X B))) ≫
      J.map (singletonLabelPayload M (product X B)) = 𝟙 _ := by
    rw [← J.map_comp, labelInject_payload, J.map_id]
  simp only [Category.assoc, untag, Category.comp_id]
  rw [← retain_q, ← Category.assoc (retainEnvironment J _ _), ← retainEnvironment_comp]
  let active := (M.productIso X A).hom ≫ snd (M.obj X) (M.obj A)
  have activeMap : J.map ((M.productIso X A).hom ≫ snd (M.obj X) (M.obj A) ≫ (λ_ (M.obj A)).inv) =
      J.map active ≫ J.map (λ_ (M.obj A)).inv := by rw [← Category.assoc, J.map_comp]
  simp only [activeMap, Category.assoc]
  change retainEnvironment J ((M.productIso X A).hom ≫ fst (M.obj X) (M.obj A))
    (J.map ((M.productIso X A).hom ≫ snd (M.obj X) (M.obj A)) ≫
      denoteSingletonRegion J M hr.hasType) ≫ _ = _
  rw [retainEnvironment_comp, retainEnvironment_map, ← CartesianMonoidalCategory.comp_lift,
    CartesianMonoidalCategory.lift_fst_snd, Category.comp_id, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationWhisker
