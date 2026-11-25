module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification

/-! # Binary-let assembly and reification in the extended singleton category -/

public section

universe u v w u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBinaryLetBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (ModelComparisons)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet
  (returnPair_typed applyPackedPair_typed literal_let₂)
open Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody (applyPacked_typed unpack_applyPacked)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (diagonal_typed returnOnce_typed unpackBody_typed)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
  (caseValueBranches seqValueBranches whiskerLeftRegion_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom literal_case_ofRegion)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {p : Region Φ}

set_option backward.isDefEq.respectTransparency false in
theorem assemble_let₂ (ha : Tm.HasType [X] a (product A B))
    (hp : ValueBranches [product X (product A B)] p [D]) :
    (ofRegion (τ := τ) (diagonal_typed (Φ := Φ) X) ≫
      (whiskerLeftFunctor (ofType (Φ := Φ) X)).map (ofRegion (τ := τ) (returnOnce_typed ha))) ≫
        ofRegion (τ := τ) hp =
      ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) := by
  have e : ofRegion (τ := τ) (returnOnce_typed ha) = ofRegion (τ := τ) (returnPair_typed ha) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff BinaryLetBind.Step _ _).2
      (Paper.WithBinaryLetBind.returnPair_eq_returnOnce ha).symm
  rw [e]
  have ew := Paper.Extension.Singleton.whiskerLeft_map BinaryLetBind.Step
    (X := Paper.TypeCategory.ofType (Φ := Φ) X) (Paper.TypeCategory.ofRegion (τ := τ) (returnPair_typed ha))
  change ((projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion (τ := τ) (diagonal_typed (Φ := Φ) X)) ≫
    (Paper.Extension.Singleton.whiskerLeftFunctor BinaryLetBind.Step
      (ofType (Φ := Φ) X)).map ((projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion (τ := τ) (returnPair_typed ha)))) ≫
        (projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion (τ := τ) hp) = _
  rw [ew, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg ((projection (τ := τ) (Φ := Φ)).map)
  rw [Paper.TypeCategory.whiskerLeft_ofRegion]
  let h := seqValueBranches (diagonal_typed (Φ := Φ) X) (whiskerLeftRegion_typed X (returnPair_typed ha))
  rw [Paper.TypeCategory.ofRegion_comp _ _ h,
    Paper.TypeCategory.ofRegion_comp h hp (seqValueBranches h hp)]
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).2 (literal_let₂ ha hp)

set_option backward.isDefEq.respectTransparency false in
private theorem case_map_congr {L R : τ} {l l' r r' : Region Φ}
    (hl : ValueBranches [L] l [D]) (hl' : ValueBranches [L] l' [D])
    (hr : ValueBranches [R] r [D]) (hr' : ValueBranches [R] r' [D])
    (el : ofRegion (τ := τ) hl = ofRegion (τ := τ) hl')
    (er : ofRegion (τ := τ) hr = ofRegion (τ := τ) hr') :
    ofRegion (τ := τ) (caseValueBranches hl hr) =
      ofRegion (τ := τ) (caseValueBranches hl' hr') := by
  have el' := (Paper.Extension.Singleton.ofRegion_eq_iff BinaryLetBind.Step hl hl').1 el
  have er' := (Paper.Extension.Singleton.ofRegion_eq_iff BinaryLetBind.Step hr hr').1 er
  apply (Paper.Extension.Singleton.ofRegion_eq_iff BinaryLetBind.Step _ _).2
  exact .case (.var (i := 0) rfl)
    (el'.renameVars ((Ren.wk [] (Silmaril.coprod L R)).lift L))
    (er'.renameVars ((Ren.wk [] (Silmaril.coprod L R)).lift R))

section Denotation

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp]
  [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option backward.isDefEq.respectTransparency false in
theorem compare_let₂ (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (product A B))
    (hp : ValueBranches [product X (product A B)] p [D])
    (hBody : (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso (denoteSingletonRegion J M hp.hasType)) = ofRegion (τ := τ) hp) :
    (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType))) =
        ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) := by
  rw [SingletonReification.factor_let₂ J M objIso pe cmp ha hp, Functor.map_comp, Functor.map_comp, hBody]
  rw [← Paper.Extension.Singleton.whiskerLeft_map BinaryLetBind.Step]
  exact assemble_let₂ ha hp

set_option backward.isDefEq.respectTransparency false in
private theorem compare_let₁ (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a A) (hp : ValueBranches [product X A] p [D])
    (hBody : (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M hp.hasType)) = ofRegion (τ := τ) hp) :
    (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M (.let₁ ha (applyPacked_typed hp).hasType))) =
        ofRegion (τ := τ) (.let₁ ha (applyPacked_typed hp)) := by
  rw [SingletonReification.factor_let₁ J M objIso pe cmp ha hp, Functor.map_comp, hBody]
  exact ((projection (τ := τ) (Φ := Φ)).map_comp _ _).symm.trans
    (congrArg (projection (τ := τ) (Φ := Φ)).map (SingletonReification.assemble_let₁ ha hp))

set_option backward.isDefEq.respectTransparency false in
private theorem compare_case (cmp : ModelComparisons J M objIso pe) {q : Region Φ}
    (ha : Tm.HasType [X] a (Silmaril.coprod A B))
    (hp : ValueBranches [product X A] p [D]) (hq : ValueBranches [product X B] q [D])
    (hLeft : (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M hp.hasType)) = ofRegion (τ := τ) hp)
    (hRight : (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M hq.hasType)) = ofRegion (τ := τ) hq) :
    (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M (.case ha (applyPacked_typed hp).hasType (applyPacked_typed hq).hasType))) =
        ofRegion (τ := τ) (.case ha (applyPacked_typed hp) (applyPacked_typed hq)) := by
  let F := projection (τ := τ) (Φ := Φ)
  obtain ⟨_, hl, el⟩ := Paper.TypeCategory.exists_ofRegion
    (reindexHom J M objIso (denoteSingletonRegion J M hp.hasType))
  obtain ⟨_, hr, er⟩ := Paper.TypeCategory.exists_ofRegion
    (reindexHom J M objIso (denoteSingletonRegion J M hq.hasType))
  have hlPack : ofRegion (τ := τ) hl = ofRegion (τ := τ) (unpackBody_typed (applyPacked_typed hp)) :=
    (congrArg F.map el).symm.trans (hLeft.trans
      (congrArg F.map ((Paper.TypeCategory.ofRegion_eq_iff _ hp).2 (unpack_applyPacked hp))).symm)
  have hrPack : ofRegion (τ := τ) hr = ofRegion (τ := τ) (unpackBody_typed (applyPacked_typed hq)) :=
    (congrArg F.map er).symm.trans (hRight.trans
      (congrArg F.map ((Paper.TypeCategory.ofRegion_eq_iff _ hq).2 (unpack_applyPacked hq))).symm)
  have assembled := literal_case_ofRegion ha (applyPacked_typed hp) (applyPacked_typed hq)
  unfold Paper.RetainedCase.assembledCaseArrow at assembled
  change F.map (reindexHom J M objIso _) =
    F.map (Paper.TypeCategory.ofRegion (.case ha (applyPacked_typed hp) (applyPacked_typed hq)))
  rw [SingletonReification.factor_case J M objIso pe cmp ha hp hq,
    SingletonReification.compare_copair J M objIso cmp.inl cmp.inr hl hr el er,
    ← assembled, Functor.map_comp, Functor.map_comp]
  exact congrArg (_ ≫ ·) (case_map_congr hl _ hr _ hlPack hrPack)

set_option backward.isDefEq.respectTransparency false in
theorem compare (cmp : ModelComparisons J M objIso pe)
    {r : Region Φ} {hr : ValueBranches [X] r [D]} (h : LoopFree hr) :
    (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso (denoteSingletonRegion J M hr.hasType)) =
      ofRegion (τ := τ) hr := by
  let F := projection (τ := τ) (Φ := Φ)
  induction h with
  | branch ha =>
    exact congrArg F.map (SingletonReification.compare J M objIso pe cmp (.branch ha))
  | let₁ ha _ ih => exact compare_let₁ J M objIso pe cmp ha _ ih
  | let₂ ha _ ih => exact compare_let₂ J M objIso pe cmp ha _ ih
  | case ha _ _ ihl ihr => exact compare_case J M objIso pe cmp ha _ _ ihl ihr
  | @cfgZero X D p hp _ blocks ih =>
    rw [denoteSingletonRegion_cfgZero J M hp.hasType blocks, ih]
    apply congrArg F.map
    exact (Paper.TypeCategory.ofRegion_eq_iff _ _).2
      (.symm (.cfgEta (.native (.base (.entry (.cfgZero hp.hasType blocks))))))

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBinaryLetBind
