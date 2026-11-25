module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Soundness.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Codiagonal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Soundness.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Step.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Soundness.Congruence
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms

/-! # Denotational soundness of the opt-in λSSA closure -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem sound
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  have common : CommonDenotation J M Γ r s L := by
    clear hr hs
    induction h with
    | cfgEta h =>
      exact CommonDenotation.of_eq (h.sound_sharedTensor J M
        (FreydCategory.CentralUnit.unit_central (J := J)) shared h.typed.1 h.typed.2)
    | productBeta h =>
      obtain ⟨_, dr, ds⟩ := h.denotes J M
      exact ⟨_, _, _, dr, ds⟩
    | productEta h =>
      obtain ⟨_, dr, ds⟩ := h.denotes J M
      exact ⟨_, _, _, dr, ds⟩
    | symm _ ih => exact ih.symm
    | trans _ _ il ir => exact il.trans ir
    | let₁ ha _ ih => exact CommonDenotation.let₁ ha ih
    | let₂ ha _ ih => exact CommonDenotation.let₂ ha ih
    | case ha _ _ il ir => exact CommonDenotation.case ha il ir
    | cfg R _ _ ie ib => exact CommonDenotation.cfg R ie ib
    | lsubstCongr hp _ ih => exact CommonDenotation.lsubstCongr shared hp ih
    | lsubstPost _ hr hs hσ ih => exact ih.lsubstPost shared hr hs hσ
    | substVars _ hθ ih => exact ih.substVars hθ
    | renameLabels _ hρ ih => exact ih.renameLabels hρ
    | collapsePost he hp hσ =>
      exact CommonDenotation.of_eq (CfgEta.Codiagonal.collapsePost M J shared he hp hσ)
    | uniform he hp hq ha _ ih =>
      obtain ⟨_, da⟩ := ha.denotes_map J M
      obtain ⟨hl, hr, _, dl, dr⟩ := ih
      exact CommonDenotation.of_eq (CfgEta.Uniformity.sound_entry_of_denotations M J shared he hp hq da
        hl hr ((dl.eq_denote J M).symm.trans (dr.eq_denote J M)))
  exact common.eq_denote hr hs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
