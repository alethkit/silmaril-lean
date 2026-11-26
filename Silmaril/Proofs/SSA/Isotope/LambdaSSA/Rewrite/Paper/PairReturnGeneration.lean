module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Return.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms

/-! # Generation and soundness for pair returns -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnGeneration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithPairReturns
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CfgEta.TypeCategory (returnRegion_typed returnRegion_branchValue)
open Paper.RetainedLet (returnOnce_typed)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff projection pairArrows map_pairArrows SeedDenotes)
open Paper.Extension.Singleton.Generation (Generated)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {ε : Type w} [HasEff Φ ε]

section Generation

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includePair : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Step Γ r s L → Seed Γ r s L)
  (includeUnary : ∀ {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}, Paper.UnaryReturn.Step Γ r s L → Seed Γ r s L)
  {X A B : τ} {a b : Tm Φ}

set_option hygiene false in
local notation "Lit" => ofRegion Seed

include includeUnary in
private theorem lowerLet {Γ : VCtx τ} {E D : τ} {s t : Tm Φ}
    (hs : Tm.HasType Γ s E) (ht : Tm.HasType (E :: Γ) t D) :
    Paper.Extension.Eqv Seed Γ (CfgEta.TypeCategory.returnRegion (.let₁ s t))
      (.let₁ s (CfgEta.TypeCategory.returnRegion t)) [D] := by
  have step := Paper.UnaryReturn.Step.fuse hs ht
  exact (Paper.UnaryReturn.returnRegion_eq_returnOnce includeUnary (.let₁ hs ht)).trans
    ((Paper.Extension.Eqv.extra step.typed.1 step.typed.2 (includeUnary step)).symm.trans
      (.let₁ hs (Paper.UnaryReturn.returnRegion_eq_returnOnce includeUnary ht).symm))

set_option backward.isDefEq.respectTransparency false in
include includePair includeUnary in
theorem returnPair_eq_pairArrows (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B) :
    Lit (returnRegion_typed (.pair ha hb)) =
      pairArrows Seed (Lit (returnRegion_typed ha)) (Lit (returnRegion_typed hb)) := by
  let P := projection Seed
  change P.map (Paper.TypeCategory.returnTerm (.pair ha hb)) =
    pairArrows Seed (P.map (Paper.TypeCategory.returnTerm ha)) (P.map (Paper.TypeCategory.returnTerm hb))
  rw [← map_pairArrows Seed, Paper.TypeCategory.pairArrows_returnTerm ha hb]
  let hw := hb.rename (Ren.wk [X] A)
  let vars : Tm.BranchValue (B :: A :: [X]) (.pair (.var 1) (.var 0) : Tm Φ) (product A B) :=
    .pair (.var rfl) (.var rfl)
  apply (ofRegion_eq_iff Seed (returnRegion_typed (.pair ha hb))
    (returnRegion_typed (.let₁ ha (.let₁ hw vars.hasType)))).2
  have lower := (lowerLet Seed includeUnary ha (.let₁ hw vars.hasType)).trans
    (.let₁ ha ((lowerLet Seed includeUnary hw vars.hasType).trans
      (.let₁ hw (.paper (.cfgEta (.native (.base (returnRegion_branchValue vars))))))))
  exact (Paper.Extension.Eqv.extra (returnOnce_typed (.pair ha hb)).hasType
    (pairSequence_typed ha hb).hasType (includePair (.seq ha hb))).trans lower.symm

include includePair includeUnary in
theorem generated_returnPair (ha : Tm.HasType [X] a A) (hb : Tm.HasType [X] b B)
    (ga : Generated Seed (Lit (returnRegion_typed ha))) (gb : Generated Seed (Lit (returnRegion_typed hb))) :
    Generated Seed (Lit (returnRegion_typed (.pair ha hb))) := by
  rw [returnPair_eq_pairArrows Seed includePair includeUnary ha hb]
  exact Generated.pair Seed ga gb

end Generation

section Soundness

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem step_denotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L h hr hs
  cases h with
  | @seq A B a b ha hb =>
    exact ⟨_, denoteRegion_spec J M hr,
      (denote_pair_boundReturn_sequencing J M
        (show At [product A B] 0 (product A B) from rfl) ha hb).symm ▸ denoteRegion_spec J M hs⟩

theorem joined_seedDenotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    (pe : ε) : SeedDenotes (Seed := JoinedStep (τ := τ) (Φ := Φ) pe) J M := by
  intro Γ r s L h hr hs
  exact h.elim (fun old =>
    ⟨_, denoteRegion_spec J M hr,
      (Paper.WithCaseAndUnaryReturns.joined_eqv_sound pe J M shared (.extra hr hs old) hr hs).symm ▸
        denoteRegion_spec J M hs⟩) (fun pair => step_denotes J M pair hr hs)

end Soundness

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnGeneration
