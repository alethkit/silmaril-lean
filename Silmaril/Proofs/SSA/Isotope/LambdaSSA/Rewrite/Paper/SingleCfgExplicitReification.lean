module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Factor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Producer.Thms

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms

/-! # Identify the explicit carried realization in the syntactic model -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open Paper.SingletonReification.SingleCfg
open CfgEta.TypeCategory (whiskerLeftRegion)
open CfgEta.TypeCategory.Retained (distributorRegion distributorRegion_typed)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

section RouteSyntax

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private def routeBranch (a : Tm Φ) (i : Nat) : Region Φ :=
  .let₂ (.pair (.var i) a) (.case (.var 0)
    (.br 0 (.inl (.pair (.var 2) (.var 0))))
    (.br 0 (.inr (.pair (.var 2) (.var 0)))))

set_option backward.isDefEq.respectTransparency false in
private theorem route_repeat {Γ : VCtx τ} {X S D : τ} {i : Nat}
    (hc : At Γ i X) (hs : At Γ 0 S) :
    Paper.Eqv Γ (routeBranch (Φ := Φ) (.inr (.var 0)) i)
      (.br 0 (.inr (.pair (.var i) (.var 0)))) [coprod (product X D) (product X S)] := by
  let R := coprod (product X D) (product X S)
  let U := coprod D S
  have cap : Tm.BranchValue Γ (.var i : Tm Φ) X := .var hc
  have state : Tm.BranchValue Γ (.var 0 : Tm Φ) S := .var hs
  have hl : ValueBranches (D :: U :: X :: Γ)
      (.br 0 (.inl (.pair (.var 2) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
  have hr : ValueBranches (S :: U :: X :: Γ)
      (.br 0 (.inr (.pair (.var 2) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inr (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
  have β := Paper.Eqv.productBeta (.let₂Beta cap (Tm.BranchValue.inr (A := D) state)
    (.case (.var (i := 0) rfl) hl.hasType hr.hasType))
  have hL : ValueBranches (D :: Γ) (.br 0 (.inl (.pair (.var (i+1)) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inl (.pair (.var ((Ren.wk Γ D) hc)) (.var (i := 0) rfl)))
  have hR : ValueBranches (S :: Γ) (.br 0 (.inr (.pair (.var (i+1)) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inr (.pair (.var ((Ren.wk Γ S) hc)) (.var (i := 0) rfl)))
  have select := Paper.Eqv.cfgEta (.native
    ((SubstitutionEquiv.base (.caseInr state.hasType hL.hasType hR.hasType)).trans
      (.letValue state hR.hasType)))
  exact β.trans select

set_option backward.isDefEq.respectTransparency false in
private theorem route_done {Γ : VCtx τ} {X S D : τ} {i : Nat}
    (hc : At Γ i X) (hd : At Γ 0 D) :
    Paper.Eqv Γ (routeBranch (Φ := Φ) (.inl (.var 0)) i)
      (.br 0 (.inl (.pair (.var i) (.var 0)))) [coprod (product X D) (product X S)] := by
  let R := coprod (product X D) (product X S)
  let U := coprod D S
  have cap : Tm.BranchValue Γ (.var i : Tm Φ) X := .var hc
  have done : Tm.BranchValue Γ (.var 0 : Tm Φ) D := .var hd
  have hl : ValueBranches (D :: U :: X :: Γ)
      (.br 0 (.inl (.pair (.var 2) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
  have hr : ValueBranches (S :: U :: X :: Γ)
      (.br 0 (.inr (.pair (.var 2) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inr (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))
  have β := Paper.Eqv.productBeta (.let₂Beta cap (Tm.BranchValue.inl (B := S) done)
    (.case (.var (i := 0) rfl) hl.hasType hr.hasType))
  have hL : ValueBranches (D :: Γ) (.br 0 (.inl (.pair (.var (i+1)) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inl (.pair (.var ((Ren.wk Γ D) hc)) (.var (i := 0) rfl)))
  have hR : ValueBranches (S :: Γ) (.br 0 (.inr (.pair (.var (i+1)) (.var 0))) : Region Φ) [R] :=
    .br rfl (.inr (.pair (.var ((Ren.wk Γ S) hc)) (.var (i := 0) rfl)))
  have select := Paper.Eqv.cfgEta (.native
    ((SubstitutionEquiv.base (.caseInl done.hasType hL.hasType hR.hasType)).trans
      (.letValue done hL.hasType)))
  exact β.trans select

set_option backward.isDefEq.respectTransparency false in
private theorem retag_distribute (X S D : τ) :
    Paper.Eqv [product X (packedExitType [S, D])]
      (compLSubst (fun _ => whiskerLeftRegion (exitDecoder (τ := τ)))
        (fun _ => distributorRegion (Φ := Φ)) 0)
      (retagPacked S D) [coprod (product X D) (product X S)] := by
  let K := packedExitType [S, D]
  let P := product X K
  let T := coprod D (empty : τ)
  let R := coprod (product X D) (product X S)
  apply Paper.Eqv.let₂ (.var (i := 0) (show At [P] 0 P from rfl))
  apply Paper.Eqv.case (.var (i := 0) (show At [K, X, P] 0 (coprod S T) from rfl))
  · exact route_repeat (Γ := [S, K, X, P]) (i := 2) (D := D) rfl rfl
  · apply Paper.Eqv.case (.var (i := 0) (show At [T, K, X, P] 0 T from rfl))
    · exact route_done (Γ := [D, T, K, X, P]) (i := 3) (S := S) rfl rfl
    · let Z : τ := empty
      have h := (((((emptyExit_typed (Φ := Φ) R).renameVars ((Ren.wk [] P).lift Z)).renameVars
        ((Ren.wk [P] X).lift Z)).renameVars ((Ren.wk [X, P] K).lift Z)).renameVars
          ((Ren.wk [K, X, P] T).lift Z)).hasType
      exact Paper.Eqv.refl h

end RouteSyntax

section RouteComparison

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open SingletonDispatcher (route_inl route_inr)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel routeEnvironment)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft splitMapCoprod)
open Paper.SingletonReification (ModelComparisons packedWhiskerLeft)
open Paper.RetainedCase (reindexHom)
open Paper.TypeCategory (ofType ofRegion sumIso sumCofan_inl_sumIso_hom sumCofan_inr_sumIso_hom)
open CfgEta.TypeCategory.Retained (packedDistributor)
open CfgEta.TypeCategory.ConstructorReification (inlMap inrMap)

universe u v u₁ v₁ w u₂ v₂

section Natural

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

set_option backward.isDefEq.respectTransparency false in
private theorem route_tensor_map {E F L R L' R' : V}
    (e : E ⟶ F) (l : L ⟶ L') (r : R ⟶ R') :
    routeEnvironment J E L R ≫ coprod.map (J.map (e ⊗ₘ l)) (J.map (e ⊗ₘ r)) =
      J.map (e ⊗ₘ coprod.map l r) ≫ routeEnvironment J F L' R' := by
  let route := routeEnvironment J E L R
  have : IsIso route := by dsimp only [route, routeEnvironment, splitMapCoprod]; infer_instance
  have hl : coprod.inl ≫ inv route = J.map (E ◁ (coprod.inl : L ⟶ L ⨿ R)) := by
    rw [← route_inl J, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hr : coprod.inr ≫ inv route = J.map (E ◁ (coprod.inr : R ⟶ L ⨿ R)) := by
    rw [← route_inr J, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  -- Test the square on the two injections of the original retained sum.
  apply (cancel_epi (inv route)).mp
  change inv route ≫ route ≫ _ = _
  rw [IsIso.inv_hom_id_assoc]
  apply coprod.hom_ext
  · rw [coprod.inl_map, reassoc_of% hl, ← J.map_comp_assoc]
    have eq : (E ◁ (coprod.inl : L ⟶ L ⨿ R)) ≫ (e ⊗ₘ coprod.map l r) =
        (e ⊗ₘ l) ≫ (F ◁ (coprod.inl : L' ⟶ L' ⨿ R')) := by
      simp only [MonoidalCategory.tensorHom_def', Category.assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, coprod.inl_map, MonoidalCategory.whiskerLeft_comp_assoc,
        MonoidalCategory.whisker_exchange e (coprod.inl : L' ⟶ L' ⨿ R')]
    rw [eq, J.map_comp_assoc, route_inl J]
  · rw [coprod.inr_map, reassoc_of% hr, ← J.map_comp_assoc]
    have eq : (E ◁ (coprod.inr : R ⟶ L ⨿ R)) ≫ (e ⊗ₘ coprod.map l r) =
        (e ⊗ₘ r) ≫ (F ◁ (coprod.inr : R' ⟶ L' ⨿ R')) := by
      simp only [MonoidalCategory.tensorHom_def', Category.assoc]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, coprod.inr_map, MonoidalCategory.whiskerLeft_comp_assoc,
        MonoidalCategory.whisker_exchange e (coprod.inr : R' ⟶ L' ⨿ R')]
    rw [eq, J.map_comp_assoc, route_inr J]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] private theorem map_split {A B C D : V} (f : A ⟶ C) (g : B ⟶ D) :
    splitMapCoprod J A B ≫ coprod.map (J.map f) (J.map g) =
      J.map (coprod.map f g) ≫ splitMapCoprod J C D := by
  apply (cancel_epi (coprodComparison J A B)).mp
  simp only [splitMapCoprod, IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · rw [coprod.inl_map, inl_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inl_map,
      J.map_comp_assoc, map_inl_inv_coprodComparison]
  · rw [coprod.inr_map, inr_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inr_map,
      J.map_comp_assoc, map_inr_inv_coprodComparison]

private theorem retain_map {E A B : V} (f : A ⟶ B) :
    retainLeft J (R := E) (J.map f) = J.map (E ◁ f) := by
  simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]

end Natural

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)

set_option backward.isDefEq.respectTransparency false in
private theorem carriedRoute_value (X S D : τ) :
    let K := packedExitType [S, D]
    carriedRoute J M objIso X S D =
      (objIso (product X K)).inv ≫
      J.map ((M.productIso X K).hom ≫
        M.obj X ◁ (exitSum M S D ≫ (M.coprodIso D S).hom)) ≫
      routeEnvironment J (M.obj X) (M.obj D) (M.obj S) ≫
      coprod.map (J.map (M.productIso X D).inv ≫ (objIso (product X D)).hom)
        (J.map (M.productIso X S).inv ≫ (objIso (product X S)).hom) := by
  let K := packedExitType [S, D]
  let E := ctxObj M [X]
  let e : E ≅ M.obj X := λ_ (M.obj X)
  let l := labelPayloadIso M D
  let r := labelPayloadIso M S
  let f := unpackLabel M [S, D] ≫ labelAppendSplit M [S] [D]
  dsimp only [carriedRoute]
  change (objIso (product X K)).inv ≫ J.map (M.productIso X K).hom ≫
    J.map (e.inv ▷ M.obj K) ≫ retainLeft J (R := E) (J.map f) ≫
    routeEnvironment J E _ _ ≫ coprod.map (paperCarrier J M objIso X D).hom (paperCarrier J M objIso X S).hom = _
  -- Each output comparison strips the singleton label and the unit before packing.
  have arm (A : τ) : (paperCarrier J M objIso X A).hom =
      J.map (e.hom ⊗ₘ (labelPayloadIso M A).hom) ≫
        (J.map (M.productIso X A).inv ≫ (objIso (product X A)).hom) := by
    simp only [paperCarrier, carriedIso, Iso.trans_hom, Functor.mapIso_hom,
      MonoidalCategory.whiskerRightIso_hom, MonoidalCategory.whiskerLeftIso_hom, Iso.symm_hom,
      MonoidalCategory.tensorHom_def', J.map_comp_assoc]
    rfl
  rw [retain_map, arm D, arm S, ← coprod.map_map, ← Category.assoc (routeEnvironment J E _ _),
    route_tensor_map J]
  simp only [Category.assoc, ← J.map_comp_assoc, MonoidalCategory.tensorHom_def']
  congr 1
  congr 1
  congr 1
  simp only [exitSum, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc (unpackLabel M [S, D]) (labelAppendSplit M [S] [D])]
  change (M.productIso X K).hom ≫ e.inv ▷ M.obj K ≫ E ◁ f ≫
      E ◁ coprod.map l.hom r.hom ≫ e.hom ▷ (M.obj D ⨿ M.obj S) =
    (M.productIso X K).hom ≫ M.obj X ◁ (f ≫ coprod.map l.hom r.hom)
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whisker_exchange_assoc e.inv,
    ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id, MonoidalCategory.id_whiskerRight,
    Category.comp_id]

variable [InstructionModel J M Φ] {ε : Type w} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
private theorem exact_sum_compare (cmp : ModelComparisons J M objIso pe) (A B : τ) :
    J.map (M.coprodIso A B).inv ≫ (objIso (coprod A B)).hom ≫ (sumIso A B).hom =
      splitMapCoprod J (M.obj A) (M.obj B) ≫ coprod.map (objIso A).hom (objIso B).hom := by
  apply (cancel_epi (coprodComparison J (M.obj A) (M.obj B))).mp
  simp only [splitMapCoprod, IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inl_map]
    have h := congrArg (fun f => (objIso A).hom ≫ f ≫ (sumIso (Φ := Φ) A B).hom) (cmp.inl A B)
    simpa only [inlMap, reindexHom, Category.assoc, Iso.hom_inv_id_assoc,
      sumCofan_inl_sumIso_hom] using h
  · rw [inr_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inr_map]
    have h := congrArg (fun f => (objIso B).hom ≫ f ≫ (sumIso (Φ := Φ) A B).hom) (cmp.inr A B)
    simpa only [inrMap, reindexHom, Category.assoc, Iso.hom_inv_id_assoc,
      sumCofan_inr_sumIso_hom] using h

set_option backward.isDefEq.respectTransparency false in
private theorem carriedRoute_factor (cmp : ModelComparisons J M objIso pe) (X S D : τ) :
    let K := packedExitType [S, D]
    let U := coprod D S
    carriedRoute J M objIso X S D =
      reindexHom J M objIso (J.map (packedWhiskerLeft M X K U (exitSum M S D))) ≫
      reindexHom J M objIso (J.map (packedDistributor M X D S)) ≫
      (sumIso (product X D) (product X S)).hom := by
  rw [carriedRoute_value]
  simp only [reindexHom, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [packedWhiskerLeft, packedDistributor]
  simp only [J.map_comp, Category.assoc]
  rw [exact_sum_compare J M objIso cmp (product X D) (product X S)]
  simp only [← J.map_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [routeEnvironment, MonoidalCategory.whiskerLeft_comp, J.map_comp, Category.assoc]
  rw [← map_split_assoc J, coprod.map_map]

set_option backward.isDefEq.respectTransparency false in
theorem carriedRoute_compare (cmp : ModelComparisons J M objIso pe) (X S D : τ) :
    carriedRoute J M objIso X S D = ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) ≫
      (sumIso (product X D) (product X S)).hom := by
  have h := cmp.whisker (Y := X) (J.map (exitSum M S D))
  rw [retain_map] at h
  simp only [← J.map_comp] at h
  change reindexHom J M objIso (J.map (packedWhiskerLeft M X _ _ (exitSum M S D))) = _ at h
  rw [carriedRoute_factor J M objIso cmp, h, exitSum_compare J M objIso pe cmp,
    Paper.SingletonReification.distributor_compare J M objIso pe cmp, exitSum_ofRegion,
    Paper.TypeCategory.whiskerLeft_ofRegion]
  let hSeq := CfgEta.TypeCategory.seqValueBranches
    (CfgEta.TypeCategory.whiskerLeftRegion_typed X (exitDecoder_typed (Φ := Φ) S D))
    (distributorRegion_typed X D S)
  have e := (Paper.TypeCategory.ofRegion_eq_iff hSeq (retagPacked_typed X S D)).2
    (retag_distribute (Φ := Φ) X S D)
  have fact := (Paper.TypeCategory.ofRegion_comp
    (CfgEta.TypeCategory.whiskerLeftRegion_typed X (exitDecoder_typed (Φ := Φ) S D))
    (distributorRegion_typed X D S) hSeq).trans e
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (sumIso (Φ := Φ) (product X D) (product X S)).hom) fact

end RouteComparison

open Paper.RetainedLet (diagonal diagonal_typed)
open CfgEta.TypeCategory (whiskerRightRegion whiskerRightBody productFstBranches)
open CategoryTheory

section PrefixSyntax
universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false in
private theorem duplicateCapture_rightFst (X S : τ) :
    let p := product X S
    Paper.Eqv [p]
      (compLSubst (fun _ => diagonal) (fun _ => whiskerRightRegion (.let₂ (.var 0) (.br 0 (.var 1)))) 0)
      (duplicateCapture : Region Φ) [product X p] := by
  let P := product X S
  let R := product X P
  let t : Tm Φ := .var 0
  let r : Region Φ := .let₂ t (.br 0 (.pair (.var 1) (.var 2)))
  have hv : Tm.BranchValue [P] t P := .var (i := 0) rfl
  have hb : HasType [P, P, P] (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.var 2))) : Region Φ) [R] :=
    .let₂ (.var (i := 1) rfl) (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 2) rfl)))
  have hβ := Paper.Eqv.productBeta (.let₂Beta hv hv hb)
  have hr : HasType [P] r [R] :=
    .let₂ hv.hasType (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 2) rfl)))
  have hη := Paper.product_variable_eta_context (i := 0) (rfl : At [P] 0 (product X S)) hr
  have hbody : HasType [S, X, S, X, P] (.br 0 (.pair (.var 1) (.pair (.var 3) (.var 2))) : Region Φ) [R] :=
    .br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 3) rfl) (.var (i := 2) rfl)))
  have inner := Paper.Eqv.productBeta (.let₂Beta
    (.var (i := 1) (rfl : At [S, X, P] 1 X)) (.var (i := 0) (rfl : At [S, X, P] 0 S)) hbody)
  exact hβ.trans (hη.symm.trans (.let₂ hv.hasType inner))


open Paper.TypeCategory (ofType ofRegion braid braidBranches)

set_option backward.isDefEq.respectTransparency false in
private theorem duplicateCapture_arrow (X S : τ) :
    let P := product X S
    Paper.TypeCategory.diagonalArrow (Φ := Φ) P ≫
      Paper.TypeCategory.whiskerRight (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) (ofType P) =
      ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S) := by
  let P := product X S
  let h := CfgEta.TypeCategory.seqValueBranches (diagonal_typed (Φ := Φ) P)
    (CfgEta.TypeCategory.whiskerRightRegion_typed P (productFstBranches X S))
  dsimp only
  rw [Paper.TypeCategory.whiskerRight_ofRegion]
  change ofRegion (τ := τ) h = _
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).2 (duplicateCapture_rightFst (Φ := Φ) X S)


set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_braid (P : τ) :
    ofRegion (τ := τ) (diagonal_typed (Φ := Φ) P) ≫ braid (Φ := Φ) P P =
      ofRegion (τ := τ) (diagonal_typed (Φ := Φ) P) := by
  let ht := diagonal_typed (Φ := Φ) P
  let hb := braidBranches (Φ := Φ) P P
  rw [show braid (Φ := Φ) P P = ofRegion (τ := τ) hb from rfl,
    Paper.TypeCategory.ofRegion_comp ht hb (CfgEta.TypeCategory.seqValueBranches ht hb)]
  apply (Paper.TypeCategory.ofRegion_eq_iff _ _).2
  exact .productBeta (.let₂Beta (.var (i := 0) (rfl : At [P] 0 P))
    (.var (i := 0) (rfl : At [P] 0 P))
    (.br rfl (.pair (.var (i := 0) rfl) (.var (i := 1) rfl)) :
      HasType [P, P, P] (.br 0 (.pair (.var 0) (.var 1)) : Region Φ) [product P P]))

end PrefixSyntax

section PrefixComparison

open CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.TypeCategory (ofType ofRegion pairArrows diagonalArrow whiskerLeft_id whiskerRight
  braid whiskerLeft whiskerLeft_braid)
open Paper.SingletonReification (ModelComparisons packedWhiskerRight packedWhiskerLeft
  packedPair packedDiagonal reindexValueHom reindexValueHom_comp
  reindexValueHom_pair_of_producer compare_duplicate_of_producer)
open Paper.RetainedCase (reindexHom)
open CfgEta.TypeCategory (seqValueBranches whiskerRightRegion_typed)
open CfgEta.TypeCategory.ConstructorReification (fstMap)

universe u v u₁ v₁ w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
theorem capturePrefix_of_rightFst (cmp : ModelComparisons J M objIso pe) (X S : τ)
    (localRight :
      let P := product X S
      reindexValueHom J M objIso (product P P) (product X P) (packedWhiskerRight M P P X (fstMap M X S)) =
        whiskerRight (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) (ofType P)) :
    capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S) := by
  let P := product X S
  have hf : reindexValueHom J M objIso P X (fstMap M X S) =
      ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S) := cmp.fst X S
  have hi : reindexValueHom J M objIso P P (𝟙 (M.obj P)) = 𝟙 (ofType P) := by
    simp [reindexValueHom, reindexHom]
  change reindexValueHom J M objIso P (product X P) (packedPair M P X P (fstMap M X S) (𝟙 (M.obj P))) = _
  have right := localRight.trans (congrArg (fun f => whiskerRight f (ofType P)) hf).symm
  rw [reindexValueHom_pair_of_producer J M objIso cmp _ _ right,
    hf, hi, pairArrows, whiskerLeft_id, Category.comp_id]
  exact duplicateCapture_arrow X S

set_option backward.isDefEq.respectTransparency false in
theorem capturePrefix_of_braid (cmp : ModelComparisons J M objIso pe) (X S : τ)
    (outputBraid : let P := product X S
      reindexValueHom J M objIso (product P X) (product X P)
        ((M.productIso P X).hom ≫ (BraidedCategory.braiding (M.obj P) (M.obj X)).hom ≫
          (M.productIso X P).inv) = braid P X) :
    capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S) := by
  let P := product X S
  let f := fstMap M X S
  let swap := (M.productIso P X).hom ≫ (BraidedCategory.braiding (M.obj P) (M.obj X)).hom ≫
    (M.productIso X P).inv
  have split : packedDiagonal M P ≫ packedWhiskerLeft M P P X f ≫ swap =
      packedPair M P X P f (𝟙 (M.obj P)) := by
    simp only [packedDiagonal, packedPair, packedWhiskerLeft, swap, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (CartesianMonoidalCategory.lift _ _) (M.obj P ◁ f),
      CartesianMonoidalCategory.lift_whiskerLeft, Category.id_comp,
      ← Category.assoc (CartesianMonoidalCategory.lift _ _), CartesianMonoidalCategory.lift_braiding_hom]
  have left : reindexValueHom J M objIso (product P P) (product P X) (packedWhiskerLeft M P P X f) =
      whiskerLeft (ofType P) (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) := by
    have h := cmp.whisker (Y := P) (J.map f)
    rw [retain_map] at h
    simpa only [packedWhiskerLeft, reindexValueHom, J.map_comp, show
      reindexHom J M objIso (J.map f) = ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S) from cmp.fst X S] using h
  have hDup : Tm.HasType [P] (.pair (.var 0) (.var 0) : Tm Φ) (product P P) :=
    .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
  change reindexValueHom J M objIso P (product X P) (packedPair M P X P f (𝟙 (M.obj P))) = _
  rw [← split, reindexValueHom_comp, reindexValueHom_comp, outputBraid, left,
    compare_duplicate_of_producer J M objIso P (cmp.producer hDup),
    whiskerLeft_braid, ← Category.assoc, diagonalArrow, diagonal_braid]
  exact duplicateCapture_arrow X S


end PrefixComparison


section ExplicitWitness

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Paper.TypeCategory (ofType ofRegion sumIso whiskerRight braid)
open Paper.Extension.Singleton (projection)
open Paper.SingletonReification (ModelComparisons packedWhiskerRight reindexValueHom)
open Paper.RetainedCase (reindexHom)
open CfgEta.TypeCategory (productFstBranches)
open CfgEta.TypeCategory.ConstructorReification (fstMap)

universe u v u₁ v₁ w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] {pe : ε}
  [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
theorem carriedStep_reconstructed_realize {X S D : τ} {b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (rightFst :
      let P := product X S
      reindexValueHom J M objIso (product P P) (product X P) (packedWhiskerRight M P P X (fstMap M X S)) =
        whiskerRight (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) (ofType P)) :
    carriedStep J M objIso X S D ((objIso (product X S)).hom ≫
      ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
      ofRegion (τ := τ) (realizePackedStep_typed hb) ≫ (sumIso (product X D) (product X S)).hom :=
  carriedStep_eq_realizePackedStep J M objIso cmp hb
    (capturePrefix_of_rightFst J M objIso cmp X S rightFst)
    (carriedRoute_compare J M objIso cmp X S D)

set_option backward.isDefEq.respectTransparency false in
private theorem reify_guardedCfg_realize_of_prefix {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (prefixEq : capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S))
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))))
    (entryIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M he.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed he)
    (blockIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M hb.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed hb) :
    let hs := realizePackedStep_typed hb
    (projection Seed).map (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) =
      (projection Seed).map (ofRegion (τ := τ) hs ≫ (sumIso (product X D) (product X S)).hom) ∧
    (projection Seed).map (reindexHom J M objIso
      (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType)) =
      Paper.Extension.Singleton.ofRegion Seed (canonicalRegion_typed he hs) ∧
    Paper.Eqv [X] (canonicalRegion X S e (realizePackedStep S D b)) (guardedCfg S D e b) [D] := by
  let F := projection Seed
  let b' := (objIso (product X S)).hom ≫ ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv
  have blockEq : reindexHom J M objIso b' = ofRegion (τ := τ) hb := by
    simp [b', reindexHom]
  have projectedStep := carriedStep_map_congr J M objIso pe cmp Seed
    (blockIH.trans (congrArg F.map blockEq).symm)
  have exactStep := carriedStep_eq_realizePackedStep J M objIso cmp hb prefixEq
    (carriedRoute_compare J M objIso cmp X S D)
  have stepEq := projectedStep.trans (congrArg F.map exactStep)
  refine ⟨stepEq, ?_, canonicalRegion_eq_guardedCfg_realize he hb⟩
  rw [compare_guardedCfg J M objIso pe cmp he hb choice]
  exact (canonicalAssembly_map_congr Seed entryIH stepEq).trans
    (congrArg F.map (canonicalAssembly_ofRegion he (realizePackedStep_typed hb)))

theorem reify_guardedCfg_realize {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (rightFst :
      let P := product X S
      reindexValueHom J M objIso (product P P) (product X P) (packedWhiskerRight M P P X (fstMap M X S)) =
        whiskerRight (ofRegion (τ := τ) (productFstBranches (Φ := Φ) X S)) (ofType P))
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))))
    (entryIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M he.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed he)
    (blockIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M hb.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed hb) :
    let hs := realizePackedStep_typed hb
    (projection Seed).map (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) =
      (projection Seed).map (ofRegion (τ := τ) hs ≫ (sumIso (product X D) (product X S)).hom) ∧
    (projection Seed).map (reindexHom J M objIso
      (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType)) =
      Paper.Extension.Singleton.ofRegion Seed (canonicalRegion_typed he hs) ∧
    Paper.Eqv [X] (canonicalRegion X S e (realizePackedStep S D b)) (guardedCfg S D e b) [D] :=
  reify_guardedCfg_realize_of_prefix J M objIso cmp Seed he hb
    (capturePrefix_of_rightFst J M objIso cmp X S rightFst) choice entryIH blockIH

theorem reify_guardedCfg_realize_of_braid {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (outputBraid : let P := product X S
      reindexValueHom J M objIso (product P X) (product X P)
        ((M.productIso P X).hom ≫ (BraidedCategory.braiding (M.obj P) (M.obj X)).hom ≫
          (M.productIso X P).inv) = braid P X)
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))))
    (entryIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M he.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed he)
    (blockIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M hb.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed hb) :
    let hs := realizePackedStep_typed hb
    (projection Seed).map (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) =
      (projection Seed).map (ofRegion (τ := τ) hs ≫ (sumIso (product X D) (product X S)).hom) ∧
    (projection Seed).map (reindexHom J M objIso
      (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType)) =
      Paper.Extension.Singleton.ofRegion Seed (canonicalRegion_typed he hs) ∧
    Paper.Eqv [X] (canonicalRegion X S e (realizePackedStep S D b)) (guardedCfg S D e b) [D] :=
  reify_guardedCfg_realize_of_prefix J M objIso cmp Seed he hb
    (capturePrefix_of_braid J M objIso cmp X S outputBraid) choice entryIH blockIH

end ExplicitWitness

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgExplicitReification
