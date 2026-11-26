module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Pure copair witnesses and sound case-return equations -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory (returnRegion returnRegion_typed caseValueBranches)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open scoped MonoidalCategory
open CfgEta.TypeCategory (returnRegion_rename)
open Paper.WithCaseReturns (Step Eqv)
open Paper.Extension.Singleton.ValueCoproducts (CopairPure copairPure_of_caseReturn)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

private theorem caseTermTyped {A B D : τ} {a b : Tm Φ} (ha : Tm.HasType [A] a D) (hb : Tm.HasType [B] b D) :
    Tm.HasType [coprod A B] (.case (.var 0) (a.rename (lift Nat.succ)) (b.rename (lift Nat.succ))) D :=
  .case (.var rfl) (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B))

theorem copairPure_of_includesCaseReturn
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (includeCase : ∀ {Γ r s L}, Step pe Γ r s L → Seed Γ r s L) :
    CopairPure Seed pe := by
  apply copairPure_of_caseReturn
  intro A B D a b ha hb pa pb
  exact .extra (returnRegion_typed (caseTermTyped ha hb)).hasType
    (caseValueBranches (returnRegion_typed ha) (returnRegion_typed hb)).hasType
    (includeCase (.split ha hb pa pb))

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem step_sound
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (e : Step pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  cases e with
  | @split A B D a b ha hb pa pb =>
    have hl := ha.rename ((Ren.wk [] (coprod A B)).lift A)
    have hright := hb.rename ((Ren.wk [] (coprod A B)).lift B)
    have he : Tm.HasType [coprod A B] (.var 0 : Tm Φ) (coprod A B) := .var rfl
    have hs' : HasType [coprod A B] (.case (.var 0)
        (returnRegion (a.rename (lift Nat.succ))) (returnRegion (b.rename (lift Nat.succ)))) [D] :=
      .case he (returnRegion_typed hl).hasType (returnRegion_typed hright).hasType
    have hs_eq : denoteRegion J M hs' = denoteRegion J M hs := by
      generalize hx : returnRegion (a.rename (lift Nat.succ)) = l at hs' ⊢
      generalize hy : returnRegion (b.rename (lift Nat.succ)) = r at hs' ⊢
      rw [returnRegion_rename] at hx hy
      subst l
      subst r
      rfl
    exact (denote_case_returnRegion_fusion J M copyCentral he hl hright).symm.trans hs_eq

theorem eqv_sound
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (e : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  apply Paper.Extension.Eqv.sound J M shared ?_ e hr hs
  intro Γ r s L h hr hs
  have eq : denoteRegion J M hr = denoteRegion J M hs := by
    rcases h with (hp | hu) | hc
    · exact hp.sound J M hr hs
    · obtain ⟨_, d, e⟩ := hu.denotes J M hr hs
      exact (d.eq_denote J M).symm.trans (e.eq_denote J M)
    · apply step_sound pe J M ?_ hc hr hs
      intro E
      obtain ⟨h, hE⟩ := shared E E
      exact Silmaril.Isotope.LetIter.Semantics.Categorical.duplicate_central_of_tensor_eqToIso J E h hE
  exact ⟨_, denoteRegion_spec J M hr, eq.symm ▸ denoteRegion_spec J M hs⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseReturns
