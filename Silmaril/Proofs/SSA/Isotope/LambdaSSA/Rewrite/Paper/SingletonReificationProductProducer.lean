module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

/-! # Product comparisons via guarded singleton returns -/

public section

universe u v w u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel pair_maps_eq_map_lift extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open Paper.SingletonReification Paper.SingletonReification.BinaryLet
open Paper.RetainedLet (returnOnce_typed returnOnce_denotation)
open Paper.RetainedCase (reindexHom)
open Paper.TypeCategory
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B : τ}

private theorem returnOnce_branchValue {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    Paper.Eqv [X] (Paper.RetainedLet.returnOnce a) (.br 0 a) [A] :=
  .cfgEta (.native (.letValue ha (.br (ℓ := 0) rfl (.var (i := 0) rfl))))

private theorem returnPair_constructor {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
    Paper.Eqv [X] (returnPair (.pair a b)) (.br 0 (.pair a b)) [product A B] :=
  .productBeta (.let₂Beta ha hb
    (.br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "C" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ ofType (Φ := Φ) T)

set_option backward.isDefEq.respectTransparency false in
theorem denote_duplicate_producer (X : τ) :
    let ht : Tm.HasType [X] (.pair (.var 0) (.var 0) : Tm Φ) (product X X) :=
      .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
    denoteSingletonRegion J M (returnOnce_typed ht).hasType = J.map (packedDiagonal M X) := by
  let ht : Tm.HasType [X] (.pair (.var 0) (.var 0) : Tm Φ) (product X X) :=
    .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
  change denoteSingletonRegion J M (returnOnce_typed ht).hasType = _
  have hd := denoteRegion_spec J M (returnOnce_typed ht).hasType
  unfold denoteSingletonRegion
  generalize denoteRegion J M (returnOnce_typed ht).hasType = f at hd ⊢
  cases hd with
  | let₁ hp hbr =>
    cases hp with
    | pair hl hr =>
      cases hl
      cases hr
      cases hbr with
      | br hvar =>
        cases hvar
        rename_i A B ha hb D hExit hVar
        have hA : X = A := Option.some.inj ha
        have hB : X = B := Option.some.inj hb
        have hD : product X X = D := Option.some.inj hExit
        subst A B D
        have hLookup : lookup M 0 (rfl : At [X] 0 X) = (λ_ (M.obj X)).hom := by
          change CartesianMonoidalCategory.snd (𝟙_ V) (M.obj X) = _
          rw [CartesianMonoidalCategory.leftUnitor_hom]
        have hBound : lookup M 0 hVar =
            CartesianMonoidalCategory.snd (ctxObj M [X]) (M.obj (product X X)) := rfl
        rw [pair_maps_eq_map_lift, ← J.map_comp, hBound]
        unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
        rw [extend_map]
        have hPayload : labelInject M 0 hExit ≫ singletonLabelPayload M (product X X) = 𝟙 _ := by
          simp [labelInject, singletonLabelPayload]
        simp only [Category.assoc, ← J.map_comp, hPayload, Category.comp_id,
          CartesianMonoidalCategory.lift_snd_assoc]
        congr 1
        unfold packedDiagonal packedPair
        simp only [← Category.assoc, CartesianMonoidalCategory.comp_lift, hLookup, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
theorem compare_duplicate_of_producer (X : τ)
    (producer :
      let ht : Tm.HasType [X] (.pair (.var 0) (.var 0) : Tm Φ) (product X X) :=
        .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
      reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ht).hasType) =
        ofRegion (returnOnce_typed ht)) :
    reindexValueHom J M objIso X (product X X) (packedDiagonal M X) = diagonalArrow (Φ := Φ) X := by
  dsimp only at producer
  rw [denote_duplicate_producer J M X] at producer
  let hx : Tm.BranchValue [X] (.var 0 : Tm Φ) X := .var (i := 0) rfl
  refine producer.trans ((ofRegion_eq_iff _ (Paper.RetainedLet.diagonal_typed X)).2 ?_)
  exact (returnPair_pair hx hx).symm.trans (returnPair_constructor hx hx)

section

variable {ε : Type w} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
theorem reindexValueHom_pair_of_producer (cmp : ModelComparisons J M objIso pe)
    (f : M.obj X ⟶ M.obj A) (g : M.obj X ⟶ M.obj B)
    (right : reindexValueHom J M objIso (product X X) (product A X) (packedWhiskerRight M X X A f) =
      whiskerRight (reindexValueHom J M objIso X A f) (ofType X)) :
    reindexValueHom J M objIso X (product A B) (packedPair M X A B f g) =
      pairArrows (reindexValueHom J M objIso X A f) (reindexValueHom J M objIso X B g) := by
  apply reindexValueHom_pair J M objIso f g
    (compare_duplicate_of_producer J M objIso X (cmp.producer (.pair (.var rfl) (.var rfl)))) right
  have retainMap : retainLeft J (R := M.obj A) (J.map g) = J.map (M.obj A ◁ g) := by
    simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]
  simpa only [reindexValueHom, packedWhiskerLeft, J.map_comp, retainMap, Category.assoc] using
    cmp.whisker (Y := A) (A := X) (B := B) (J.map g)

end

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
theorem compare_branch_of_producer {a : Tm Φ} (ha : Tm.BranchValue [X] a A)
    (producer : reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ha.hasType).hasType) =
      ofRegion (returnOnce_typed ha.hasType)) :
    reindexHom J M objIso (denoteSingletonRegion J M (HasType.br (ℓ := 0) rfl ha.hasType)) =
      ofRegion (.br (ℓ := 0) rfl ha) := by
  have d := denote_spec J M ha.hasType
  rw [denoteSingletonRegion_br J M d, ← returnOnce_denotation J M ha.hasType d, producer]
  exact (ofRegion_eq_iff _ _).2 (returnOnce_branchValue ha)

set_option backward.isDefEq.respectTransparency false in
theorem compare_constructor_pair_of_producer {a b : Tm Φ}
    (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B)
    {f : ctxObj M [X] ⟶ M.obj A} {g : ctxObj M [X] ⟶ M.obj B}
    (df : Denotes J M ha.hasType (J.map f)) (dg : Denotes J M hb.hasType (J.map g))
    (producer : reindexHom J M objIso
      (denoteSingletonRegion J M (returnOnce_typed (.pair ha.hasType hb.hasType)).hasType) =
        ofRegion (returnOnce_typed (.pair ha.hasType hb.hasType))) :
    reindexValueHom J M objIso X (product A B)
        (packedPair M X A B ((λ_ (M.obj X)).inv ≫ f) ((λ_ (M.obj X)).inv ≫ g)) =
      ofRegion (.br (ℓ := 0) rfl (.pair ha hb)) := by
  have d : Denotes J M (.pair ha.hasType hb.hasType)
      (J.map (CartesianMonoidalCategory.lift f g ≫ (M.productIso A B).inv)) := by
    simpa only [pair_maps_eq_map_lift J, ← J.map_comp] using Denotes.pair df dg
  rw [returnOnce_denotation J M _ d, ← J.map_comp, ← Category.assoc,
    CartesianMonoidalCategory.comp_lift] at producer
  calc
    _ = ofRegion (returnOnce_typed (.pair ha.hasType hb.hasType)) := producer
    _ = ofRegion (returnPair_typed (.pair ha.hasType hb.hasType)) :=
      (ofRegion_eq_iff _ _).2 (returnPair_pair ha hb).symm
    _ = _ := (ofRegion_eq_iff _ _).2 (returnPair_constructor ha hb)


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationProductProducer
