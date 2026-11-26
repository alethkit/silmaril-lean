module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Producer.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # Ambient and syntactic comparisons for the packed swap -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Paper.RetainedLet (returnOnce returnOnce_typed)
open Paper.WithProjectionReturns (fstTerm)
open Paper.TypeCategory (braid braidRegion braidBranches ofType ofRegion ofRegion_eq_iff pairArrows)
open CfgEta.TypeCategory (productFstBranches productSndBranches)
open Paper.SingletonReification (ModelComparisons packedPair packedWhiskerRight reindexValueHom
  reindexValueHom_pair_of_producer packedSwap swapTerm)
open Paper.RetainedCase (reindexHom)
open CfgEta.TypeCategory.ConstructorReification (fstMap sndMap inlMap inrMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open SingletonDispatcher (labelInject_payload)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel extend_map pair_maps_eq_map_lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind)

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap

universe u v u₁ u₂ v₁ v₂ w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

section Values

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [HasFiniteCoproducts V] (M : TypeModel τ V)

set_option backward.isDefEq.respectTransparency false in
theorem packedSwap_pair (A B : τ) :
    packedSwap M A B = packedPair M (product A B) B A (sndMap M A B) (fstMap M A B) := by
  unfold packedSwap packedPair sndMap fstMap
  rw [← Category.assoc, ← CartesianMonoidalCategory.lift_snd_fst, CartesianMonoidalCategory.comp_lift]

/-- Reassociate the environment after reading and unpacking its singleton product input. -/
private noncomputable def unpackCtx (A B : τ) :
    ctxObj M [product A B] ⟶ ctxObj M [B, A,product A B] :=
  let E := ctxObj M [product A B]
  lift (𝟙 E) (snd (𝟙_ V) (M.obj (product A B))) ≫
    ((𝟙 E) ⊗ₘ (M.productIso A B).hom) ≫ (ctxPairIso M [product A B] A B).hom

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] in
private theorem unpack_fst (A B : τ) :
    unpackCtx M A B ≫ lookup M 1 (rfl : At [B, A,product A B] 1 A) =
      snd (𝟙_ V) (M.obj (product A B)) ≫ fstMap M A B := by
  let E := ctxObj M [product A B]
  change _ ≫ (fst (E ⊗ M.obj A) (M.obj B) ≫ snd E (M.obj A)) = _
  have h : (ctxPairIso M [product A B] A B).hom ≫ fst (E ⊗ M.obj A) (M.obj B) ≫ snd E (M.obj A) =
      snd E (M.obj A ⊗ M.obj B) ≫ fst (M.obj A) (M.obj B) :=
    CartesianMonoidalCategory.associator_inv_fst_snd E (M.obj A) (M.obj B)
  simp only [unpackCtx, Category.assoc, h, fstMap]
  dsimp only [E]
  rw [CartesianMonoidalCategory.tensorHom_snd_assoc, CartesianMonoidalCategory.lift_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] in
private theorem unpack_snd (A B : τ) :
    unpackCtx M A B ≫ lookup M 0 (rfl : At [B, A,product A B] 0 B) =
      snd (𝟙_ V) (M.obj (product A B)) ≫ sndMap M A B := by
  let E := ctxObj M [product A B]
  change _ ≫ snd (E ⊗ M.obj A) (M.obj B) = _
  have h : (ctxPairIso M [product A B] A B).hom ≫ snd (E ⊗ M.obj A) (M.obj B) =
      snd E (M.obj A ⊗ M.obj B) ≫ snd (M.obj A) (M.obj B) :=
    CartesianMonoidalCategory.associator_inv_snd E (M.obj A) (M.obj B)
  simp only [unpackCtx, Category.assoc, h, sndMap]
  dsimp only [E]
  rw [CartesianMonoidalCategory.tensorHom_snd_assoc, CartesianMonoidalCategory.lift_snd_assoc]

end Values

theorem swapTerm_typed (A B : τ) :
    Tm.HasType [product A B] (swapTerm (Φ := Φ)) (product B A) :=
  .let₂ (.var (i := 0) rfl) (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))


section Denotation

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J] (M : TypeModel τ V) [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
private theorem bindProduct (A B : τ) {Y : V}
    (g : ctxObj M [B, A,product A B] ⟶ Y) :
    bind J (J.map (lookup M 0 (rfl : At [product A B] 0 (product A B))))
      (J.map ((𝟙 (ctxObj M [product A B])) ⊗ₘ (M.productIso A B).hom) ≫
        J.map (ctxPairIso M [product A B] A B).hom ≫ J.map g) =
      J.map (unpackCtx M A B ≫ g) := by
  change Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend J
    (J.map (snd (𝟙_ V) (M.obj (product A B)))) ≫ _ = _
  rw [extend_map]
  simp only [unpackCtx, J.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem swapBody_denotes (A B : τ) :
    Denotes J M (.pair (.var (i := 0) (rfl : At [B, A,product A B] 0 B))
      (.var (i := 1) (rfl : At [B, A,product A B] 1 A)) :
        Tm.HasType [B, A,product A B] (.pair (.var 0) (.var 1) : Tm Φ) (product B A))
      (J.map (lift (lookup M 0 (rfl : At [B, A,product A B] 0 B))
        (lookup M 1 (rfl : At [B, A,product A B] 1 A)) ≫ (M.productIso B A).inv)) := by
  rw [J.map_comp, ← pair_maps_eq_map_lift]
  exact .pair (.var rfl) (.var rfl)

set_option backward.isDefEq.respectTransparency false in
omit [DistributiveTensor V] in
private theorem unpack_swap (A B : τ) :
    unpackCtx M A B ≫ (lift (lookup M 0 (rfl : At [B, A,product A B] 0 B))
        (lookup M 1 (rfl : At [B, A,product A B] 1 A)) ≫ (M.productIso B A).inv) =
      snd (𝟙_ V) (M.obj (product A B)) ≫ packedSwap M A B := by
  rw [packedSwap_pair, packedPair, ← Category.assoc, CartesianMonoidalCategory.comp_lift,
    unpack_snd, unpack_fst, ← CartesianMonoidalCategory.comp_lift, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem swapTerm_denotes (A B : τ) :
    Denotes J M (swapTerm_typed (Φ := Φ) A B)
      (J.map (snd (𝟙_ V) (M.obj (product A B)) ≫ packedSwap M A B)) := by
  have d := Denotes.let₂ (J := J) (M := M) (Φ := Φ) (.var (rfl : At [product A B] 0 (product A B))) (swapBody_denotes J M A B)
  rw [bindProduct J M, unpack_swap] at d
  exact d

set_option backward.isDefEq.respectTransparency false in
private theorem firstTerm_denotes (A B : τ) :
    Denotes J M (fstTerm (Φ := Φ) A B)
      (J.map (snd (𝟙_ V) (M.obj (product A B)) ≫ fstMap M A B)) := by
  have d := Denotes.let₂ (J := J) (M := M) (Φ := Φ)
    (.var (rfl : At [product A B] 0 (product A B))) (.var (i := 1) (rfl : At [B, A,product A B] 1 A))
  rw [bindProduct J M, unpack_fst] at d
  exact d

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap

universe u v u₁ u₂ v₁ v₂ w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

section Region

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem braid_denotes (A B : τ) :
    RegionDenotes J M (braidBranches (Φ := Φ) A B).hasType
      (J.map (snd (𝟙_ V) (M.obj (product A B)) ≫ packedSwap M A B ≫
        labelInject M 0 (rfl : At [product B A] 0 (product B A)))) := by
  have d := RegionDenotes.let₂ (J := J) (M := M)
    (.var (rfl : At [product A B] 0 (product A B)))
    (RegionDenotes.br (h := (rfl : At [product B A] 0 (product B A))) (swapBody_denotes J M (Φ := Φ) A B))
  rw [← J.map_comp, bindProduct J M, ← Category.assoc, unpack_swap] at d
  simpa only [Category.assoc] using d

set_option backward.isDefEq.respectTransparency false in
private theorem returnOnce_map_denotes {P Q : τ} {a : Tm Φ} {ha : Tm.HasType [P] a Q}
    {f : ctxObj M [P] ⟶ M.obj Q} (h : Denotes J M ha (J.map f)) :
    RegionDenotes J M (returnOnce_typed ha).hasType
      (J.map (f ≫ labelInject M 0 (rfl : At [Q] 0 Q))) := by
  have out := RegionDenotes.br (h := (rfl : At [Q] 0 Q))
    (Denotes.var (J := J) (M := M) (Φ := Φ) (rfl : At [Q, P] 0 Q))
  have d := RegionDenotes.let₁ h out
  change RegionDenotes J M (returnOnce_typed ha).hasType
    (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.extend J (J.map f) ≫
      J.map (snd (ctxObj M [P]) (M.obj Q)) ≫ J.map (labelInject M 0 (rfl : At [Q] 0 Q))) at d
  rw [extend_map, ← J.map_comp_assoc, CartesianMonoidalCategory.lift_snd, ← J.map_comp] at d
  exact d

theorem swapReturn_denotes (A B : τ) :
    RegionDenotes J M (returnOnce_typed (swapTerm_typed (Φ := Φ) A B)).hasType
      (J.map (snd (𝟙_ V) (M.obj (product A B)) ≫ packedSwap M A B ≫
        labelInject M 0 (rfl : At [product B A] 0 (product B A)))) := by
  have eq := congrArg J.map (Category.assoc (snd (𝟙_ V) (M.obj (product A B)))
    (packedSwap M A B) (labelInject M 0 (rfl : At [product B A] 0 (product B A))))
  exact eq ▸ returnOnce_map_denotes J M (swapTerm_denotes J M (Φ := Φ) A B)

variable [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
private theorem denoteSingleton_productGraph {P Q : τ} {r : Region Φ}
    {hr : HasType [P] r [Q]} {f : M.obj P ⟶ M.obj Q}
    (d : RegionDenotes J M hr
      (J.map (snd (𝟙_ V) (M.obj P) ≫ f ≫ labelInject M 0 (rfl : At [Q] 0 Q)))) :
    denoteSingletonRegion J M hr = J.map f := by
  rw [denoteSingletonRegion, ← d.eq_denote J M,
    ← J.map_comp_assoc, CartesianMonoidalCategory.leftUnitor_inv_snd_assoc, ← J.map_comp]
  simp only [Category.assoc, labelInject_payload M Q, Category.comp_id]

theorem denoteSingleton_braid (A B : τ) :
    denoteSingletonRegion J M (braidBranches (Φ := Φ) A B).hasType = J.map (packedSwap M A B) :=
  denoteSingleton_productGraph J M (braid_denotes J M A B)

theorem denoteSingleton_swapTerm (A B : τ) :
    denoteSingletonRegion J M (returnOnce_typed (swapTerm_typed (Φ := Φ) A B)).hasType =
      J.map (packedSwap M A B) :=
  denoteSingleton_productGraph J M (swapReturn_denotes J M A B)

theorem denoteSingleton_firstTerm (A B : τ) :
    denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) A B)).hasType =
      J.map (fstMap M A B) :=
  denoteSingleton_productGraph J M (by
    have eq := congrArg J.map (Category.assoc (snd (𝟙_ V) (M.obj (product A B)))
      (fstMap M A B) (labelInject M 0 (rfl : At [A] 0 A)))
    exact eq ▸ returnOnce_map_denotes J M (firstTerm_denotes J M (Φ := Φ) A B))

set_option backward.isDefEq.respectTransparency false in
private theorem denoteSingleton_let₂_var_branch_of_map (A S D : τ) {a : Tm Φ}
    {ha : Tm.HasType [S, A, product A S] a D}
    {g : ctxObj M [S, A, product A S] ⟶ M.obj D}
    (da : Denotes J M ha (J.map g)) :
    denoteSingletonRegion J M (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl ha) :
      HasType [product A S] (.let₂ (.var 0) (.br 0 a)) [D]) =
        J.map ((λ_ (M.obj (product A S))).inv ≫ unpackCtx M A S ≫ g) := by
  have graph := RegionDenotes.let₂ (J := J) (M := M)
    (.var (rfl : At [product A S] 0 (product A S)))
    (RegionDenotes.br (h := (rfl : At [D] 0 D)) da)
  rw [← J.map_comp, bindProduct J M] at graph
  rw [denoteSingletonRegion, ← graph.eq_denote J M, ← J.map_comp_assoc, ← J.map_comp]
  simp only [Category.assoc, labelInject_payload M D, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem exists_denoteSingleton_let₂_var_branch (A S D : τ) {a : Tm Φ}
    (ha : Tm.BranchValue [S, A, product A S] a D) :
    ∃ f : M.obj (product A S) ⟶ M.obj D,
      denoteSingletonRegion J M (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl ha.hasType) :
        HasType [product A S] (.let₂ (.var 0) (.br 0 a)) [D]) = J.map f := by
  obtain ⟨g, dg⟩ := ha.denotes_map J M
  exact ⟨_, denoteSingleton_let₂_var_branch_of_map J M A S D dg⟩

set_option backward.isDefEq.respectTransparency false in
theorem denoteSingleton_let₂_resultTag (A S D : τ) {a : Tm Φ}
    (ha : Tm.BranchValue [S, A, product A S] a D) :
    denoteSingletonRegion J M
        (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.inr (.inl ha.hasType))) :
          HasType [product A S] (.let₂ (.var 0) (.br 0 (.inr (.inl a)))) [packedExitType [S, D]]) =
      denoteSingletonRegion J M
        (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl ha.hasType) :
          HasType [product A S] (.let₂ (.var 0) (.br 0 a)) [D]) ≫
        J.map (inlMap M D Silmaril.empty ≫ inrMap M S (coprod D Silmaril.empty)) := by
  obtain ⟨g, dg⟩ := ha.denotes_map J M
  have tag := Denotes.inr (A := S) (Denotes.inl (B := Silmaril.empty) dg)
  rw [Category.assoc] at tag
  change Denotes J M (.inr (.inl ha.hasType))
    (J.map g ≫ J.map (inlMap M D Silmaril.empty) ≫ J.map (inrMap M S (coprod D Silmaril.empty))) at tag
  rw [← J.map_comp_assoc, ← J.map_comp] at tag
  rw [denoteSingleton_let₂_var_branch_of_map J M A S _ tag, denoteSingleton_let₂_var_branch_of_map J M A S D dg,
    ← J.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem denoteSingleton_productFst (A S : τ) :
    denoteSingletonRegion J M (productFstBranches (Φ := Φ) A S).hasType = J.map (fstMap M A S) := by
  rw [denoteSingleton_let₂_var_branch_of_map J M A S A
      (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 1) (rfl : At [S, A, product A S] 1 A)),
    unpack_fst, CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem denoteSingleton_snd_repeatTag (A S D : τ) :
    denoteSingletonRegion J M
      (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))) :
        HasType (Φ := Φ) [product A S] (.let₂ (.var 0) (.br 0 (.inl (.var 0)))) [packedExitType [S, D]]) =
      J.map (sndMap M A S ≫ inlMap M S (coprod D Silmaril.empty)) := by
  have tag := Denotes.inl (B := coprod D Silmaril.empty)
    (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At [S, A, product A S] 0 S))
  change Denotes J M (.inl (.var (i := 0) rfl))
    (J.map (lookup M 0 (rfl : At [S, A, product A S] 0 S)) ≫
      J.map (inlMap M S (coprod D Silmaril.empty))) at tag
  rw [← J.map_comp] at tag
  rw [denoteSingleton_let₂_var_branch_of_map J M A S _ tag, reassoc_of% (unpack_snd M A S),
    CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]

end Region

section Syntax

open Paper.TypeCategory (diagonalArrow whiskerRight_ofRegion whiskerLeft_ofRegion tensorObj ofRegion_comp)
open Paper.RetainedLet (diagonal_typed)
open CfgEta.TypeCategory (seqValueBranches whiskerLeftRegion_typed whiskerRightRegion_typed)
open Paper (Eqv)

set_option backward.isDefEq.respectTransparency false in
theorem pair_projections_braid (A B : τ) :
    pairArrows (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B))
      (ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)) = braid A B := by
  let P := product A B
  let hSnd := productSndBranches (Φ := Φ) A B
  let hFst := productFstBranches (Φ := Φ) A B
  let hd := diagonal_typed (Φ := Φ) P
  let hr := whiskerRightRegion_typed P hSnd
  let hl := whiskerLeftRegion_typed B hFst
  let hPair := seqValueBranches hd (seqValueBranches hr hl)
  let hBraid := braidBranches (Φ := Φ) A B
  unfold pairArrows diagonalArrow braid
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  unfold tensorObj
  erw [ofRegion_comp _ _ (seqValueBranches hr hl), ofRegion_comp _ _ hPair]
  apply (ofRegion_eq_iff hPair hBraid).2
  apply (Paper.product_variable_eta_iff (i := 0) (A := A) (B := B)
    (rfl : At [P] 0 P) hPair.hasType hBraid.hasType).1
  let Δ : VCtx τ := [B, A, P]
  have x : Tm.BranchValue Δ (.var 1 : Tm Φ) A := .var rfl
  have y : Tm.BranchValue Δ (.var 0 : Tm Φ) B := .var rfl
  have xy := Tm.BranchValue.pair x y
  change Eqv Δ (.let₂ (.pair (.pair (.var 1) (.var 0)) (.pair (.var 1) (.var 0)))
      (.let₂ (.var 1) (.let₂ (.pair (.var 0) (.var 2))
        (.let₂ (.var 0) (.br 0 (.pair (.var 3) (.var 1)))))))
    (.let₂ (.pair (.var 1) (.var 0)) (.br 0 (.pair (.var 0) (.var 1)))) [product B A]
  apply Eqv.trans _ (.symm (.productBeta (.let₂Beta x y
    (.br rfl (.pair (.var (i := 0) rfl) (.var (i := 1) rfl))))))
  refine Eqv.trans (.productBeta (.let₂Beta xy xy
    (.let₂ (A := A) (B := B) (.var rfl)
      (.let₂ (A := B) (B := P) (.pair (.var rfl) (.var rfl))
        (.let₂ (A := A) (B := B) (.var rfl)
          (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)))))))) ?_
  refine Eqv.trans (.productBeta (.let₂Beta x y
    (.let₂ (A := B) (B := P) (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
      (.let₂ (A := A) (B := B) (.var rfl)
        (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 1) rfl))))))) ?_
  refine Eqv.trans (.productBeta (.let₂Beta y xy
    (.let₂ (A := A) (B := B) (.var rfl)
      (.br rfl (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)))))) ?_
  exact .productBeta (.let₂Beta x y (.br rfl (.pair (.var (i := 2) rfl) (.var (i := 1) rfl))))

end Syntax

section Transport

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp] [HasFiniteCoproducts V]
  [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
private theorem transport_swap_pair (cmp : ModelComparisons J M objIso pe) (A B : τ)
    (rightSnd :
      let P := product A B
      reindexValueHom J M objIso (product P P) (product B P) (packedWhiskerRight M P P B (sndMap M A B)) =
        Paper.TypeCategory.whiskerRight (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B)) (ofType P)) :
    reindexValueHom J M objIso (product A B) (product B A) (packedSwap M A B) =
      pairArrows (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B))
        (ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)) := by
  have e := congrArg (fun f => Paper.TypeCategory.whiskerRight f (ofType (Φ := Φ) (product A B))) (cmp.snd A B)
  rw [packedSwap_pair, reindexValueHom_pair_of_producer J M objIso cmp _ _ (rightSnd.trans e.symm)]
  exact congrArg₂ pairArrows (cmp.snd A B) (cmp.fst A B)

theorem compare_swap_of_rightSnd (cmp : ModelComparisons J M objIso pe) (A B : τ)
    (rightSnd :
      let P := product A B
      reindexValueHom J M objIso (product P P) (product B P) (packedWhiskerRight M P P B (sndMap M A B)) =
        Paper.TypeCategory.whiskerRight (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B)) (ofType P)) :
    reindexValueHom J M objIso (product A B) (product B A) (packedSwap M A B) = braid A B :=
  (transport_swap_pair J M objIso cmp A B rightSnd).trans (pair_projections_braid A B)

variable [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
theorem compare_swap_iff_return (A B : τ)
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (swapTerm_typed (Φ := Φ) A B)).hasType) =
        ofRegion (τ := τ) (returnOnce_typed (swapTerm_typed (Φ := Φ) A B))) :
    reindexValueHom J M objIso (product A B) (product B A) (packedSwap M A B) = braid A B ↔
      Paper.Eqv [product A B] (returnOnce (swapTerm (Φ := Φ))) braidRegion [product B A] := by
  rw [denoteSingleton_swapTerm J M] at producer
  change reindexValueHom J M objIso _ _ _ = _ at producer
  rw [producer]
  exact ofRegion_eq_iff (returnOnce_typed (swapTerm_typed (Φ := Φ) A B)) (braidBranches A B)

set_option backward.isDefEq.respectTransparency false in
theorem projection_comparisons_force_return (A B : τ)
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (fstTerm (Φ := Φ) A B)).hasType) =
        ofRegion (τ := τ) (returnOnce_typed (fstTerm (Φ := Φ) A B)))
    (projection : reindexValueHom J M objIso (product A B) A (fstMap M A B) =
      ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)) :
    Paper.Eqv [product A B] (returnOnce (.let₂ (.var 0) (.var 1) : Tm Φ))
      (.let₂ (.var 0) (.br 0 (.var 1))) [A] := by
  rw [denoteSingleton_firstTerm J M] at producer
  exact (ofRegion_eq_iff _ (productFstBranches A B)).1 (producer.symm.trans projection)

end Transport

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationSwap
