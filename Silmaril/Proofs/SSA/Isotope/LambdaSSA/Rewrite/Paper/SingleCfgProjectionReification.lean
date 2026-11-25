module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Reification.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Return.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Product.Swap.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Thms

/-! # Local reification by the existing projection-return equations -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.TypeCategory (braidBranches)
open Paper.RetainedLet (returnOnce_typed)
open CfgEta.TypeCategory (productFstBranches productSndBranches returnRegion returnRegion_typed seqValueBranches)
open Paper.WithProjectionReturns (fstTerm sndTerm Step)
open Paper.Extension.Singleton (ofRegion_eq_iff map_pairArrows)

open Paper.WithProjectionReturns.Reification

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Seed" => (Step (τ := τ) (Φ := Φ))
local notation "Q" => Paper.Extension.Singleton.ofRegion Seed
local notation "F" => Paper.Extension.Singleton.projection Seed

private theorem pairTerm_typed {X A B : τ} {a b : Tm Φ}
    (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B) :
    Tm.HasType [X] (pairTerm a b) (product A B) :=
  .let₁ ha (.let₁ (hb.rename (Ren.wk [X] A))
    (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))

theorem rebuildPair_typed (A B : τ) :
    Tm.HasType [product A B] (rebuildPair (Φ := Φ)) (product A B) :=
  pairTerm_typed (fstTerm A B) (sndTerm A B)

theorem swapPair_typed (A B : τ) :
    Tm.HasType [product A B] (swapPair (Φ := Φ)) (product B A) :=
  pairTerm_typed (sndTerm A B) (fstTerm A B)

set_option backward.isDefEq.respectTransparency false in
private theorem pairTerm_arrow {X A B : τ} {a b : Tm Φ}
    (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B) :
    Q (returnRegion_typed (pairTerm_typed ha hb)) =
      Paper.Extension.Singleton.pairArrows Seed (Q (returnRegion_typed ha)) (Q (returnRegion_typed hb)) := by
  have e := congrArg (F).map (Paper.TypeCategory.pairArrows_returnTerm ha hb)
  rw [map_pairArrows] at e
  exact e.symm

private theorem fst_arrow_eq (A B : τ) :
    Q (returnOnce_typed (fstTerm (Φ := Φ) A B)) = Q (productFstBranches A B) :=
  (ofRegion_eq_iff Seed _ _).2 (Paper.WithProjectionReturns.Step.eqv (.fst A B))

private theorem snd_arrow_eq (A B : τ) :
    Q (returnOnce_typed (sndTerm (Φ := Φ) A B)) = Q (productSndBranches A B) :=
  (ofRegion_eq_iff Seed _ _).2 (Paper.WithProjectionReturns.Step.eqv (.snd A B))

set_option backward.isDefEq.respectTransparency false in
theorem rebuildPair_arrow (A B : τ) :
    Q (returnRegion_typed (rebuildPair_typed (Φ := Φ) A B)) =
      𝟙 (Paper.Extension.Singleton.ofType Seed (product A B)) := by
  have h := pairTerm_arrow (fstTerm (Φ := Φ) A B) (sndTerm A B)
  rw [fst_arrow_eq, snd_arrow_eq] at h
  have h' := congrArg (F).map (Paper.TypeCategory.pairArrows_projections (Φ := Φ) A B)
  rw [map_pairArrows] at h'
  exact h.trans (h'.trans ((F).map_id (Paper.TypeCategory.ofType (Φ := Φ) (product A B))))

set_option backward.isDefEq.respectTransparency false in
theorem swapPair_arrow (A B : τ) :
    Q (returnRegion_typed (swapPair_typed (Φ := Φ) A B)) = Q (braidBranches A B) := by
  have h := pairTerm_arrow (sndTerm (Φ := Φ) A B) (fstTerm A B)
  rw [snd_arrow_eq, fst_arrow_eq] at h
  have h' := congrArg (F).map (Paper.SingletonReification.pair_projections_braid (Φ := Φ) A B)
  rw [map_pairArrows] at h'
  exact h.trans h'

theorem afterRebuild_typed {A B D : τ} {p : Region Φ} (hp : ValueBranches [product A B] p [D]) :
    ValueBranches [product A B] (afterRebuild p) [D] :=
  seqValueBranches (returnRegion_typed (rebuildPair_typed A B)) hp

set_option backward.isDefEq.respectTransparency false in
theorem afterRebuild_arrow {A B D : τ} {p : Region Φ} (hp : ValueBranches [product A B] p [D]) :
    Q (afterRebuild_typed hp) = Q hp := by
  have h := congrArg (F).map (Paper.TypeCategory.ofRegion_comp
    (returnRegion_typed (rebuildPair_typed (Φ := Φ) A B)) hp (afterRebuild_typed hp))
  rw [Functor.map_comp] at h
  change Q (returnRegion_typed (rebuildPair_typed A B)) ≫ Q hp = Q (afterRebuild_typed hp) at h
  rw [rebuildPair_arrow, Category.id_comp] at h
  exact h.symm

open Paper.SingletonReification.SingleCfg (guardedCfg_typed guardedCfg_map_congr)

theorem guardedCfg_afterRebuild_arrow {A B S D : τ} {e b : Region Φ}
    (he : ValueBranches [product A B] e [packedExitType [S, D]])
    (hb : ValueBranches [product (product A B) S] b [packedExitType [S, D]]) :
    Q (guardedCfg_typed (afterRebuild_typed he) (afterRebuild_typed hb)) =
      Q (guardedCfg_typed he hb) :=
  guardedCfg_map_congr Seed _ he _ hb (afterRebuild_arrow he) (afterRebuild_arrow hb)

section Ambient

open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
private theorem denote_of_arrow_eq
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {A B : τ} {p q : Region Φ} (hp : ValueBranches [A] p [B]) (hq : ValueBranches [A] q [B])
    (eq : Q hp = Q hq) :
    denoteSingletonRegion J M hp.hasType = denoteSingletonRegion J M hq.hasType := by
  have rewrite := (ofRegion_eq_iff Seed hp hq).1 eq
  have e := Paper.WithProjectionReturns.Eqv.sound J M shared rewrite hp.hasType hq.hasType
  unfold denoteSingletonRegion
  rw [e]

/-- The rebuilt input gives both the same ambient arrow and the same opt-in quotient representative. -/
theorem afterRebuild_compare
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {A B D : τ} {p : Region Φ} (hp : ValueBranches [product A B] p [D]) :
    let hr := afterRebuild_typed hp
    denoteSingletonRegion J M hr.hasType = denoteSingletonRegion J M hp.hasType ∧ Q hr = Q hp :=
  ⟨denote_of_arrow_eq J M shared _ hp (afterRebuild_arrow hp), afterRebuild_arrow hp⟩

/-- The sequential producer represents the ambient packed swap and the projected guarded braid. -/
theorem swapPair_compare
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (A B : τ) :
    let hr := returnRegion_typed (swapPair_typed (Φ := Φ) A B)
    denoteSingletonRegion J M hr.hasType = J.map (Paper.SingletonReification.packedSwap M A B) ∧
      Q hr = Q (braidBranches A B) :=
  ⟨(denote_of_arrow_eq J M shared _ _ (swapPair_arrow A B)).trans
    (Paper.SingletonReification.denoteSingleton_braid J M A B), swapPair_arrow A B⟩

theorem guardedCfg_afterRebuild_compare
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {A B S D : τ} {e b : Region Φ}
    (he : ValueBranches [product A B] e [packedExitType [S, D]])
    (hb : ValueBranches [product (product A B) S] b [packedExitType [S, D]]) :
    let hp := guardedCfg_typed (afterRebuild_typed he) (afterRebuild_typed hb)
    let hq := guardedCfg_typed he hb
    denoteSingletonRegion J M hp.hasType = denoteSingletonRegion J M hq.hasType ∧ Q hp = Q hq :=
  ⟨denote_of_arrow_eq J M shared _ _ (guardedCfg_afterRebuild_arrow he hb),
    guardedCfg_afterRebuild_arrow he hb⟩

end Ambient

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgProjectionReification
