module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Projections.Thms

/-! # Pure and central copying witnesses for the projected projections -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithProjectionReturnValues

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns (Step fstTerm sndTerm)
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion returnRegion_typed productFstBranches
  productSndBranches)
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeStep : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Step Γ r s L → Seed Γ r s L)

include includeStep in
private theorem mem_of_step {A B : τ} {a : Tm Φ} {r : Region Φ}
    (ha : Tm.HasType [A] a B) (hp : Tm.Pure pe a) (hr : ValueBranches [A] r [B])
    (hc : Paper.TypeCategory.CentralCopies (Paper.TypeCategory.ofRegion (τ := τ) hr))
    (e : Step [A] (returnRegion a) r [B]) :
    ProjectedCopyingReturn Seed pe (ofRegion Seed hr) := by
  have h : Paper.Extension.Eqv Seed [A] (returnRegion a) r [B] :=
    .extra (returnRegion_typed ha).hasType hr.hasType (includeStep e)
  refine ⟨⟨Paper.TypeCategory.returnTerm (τ := τ) ha, Paper.TypeCategory.pureReturn_returnTerm (τ := τ) pe ha hp, ?_⟩,
    ⟨Paper.TypeCategory.ofRegion (τ := τ) hr, hc, rfl⟩⟩
  exact (ofRegion_eq_iff (τ := τ) Seed (returnRegion_typed ha) hr).2 h

include includeStep in
theorem fst_mem (A B : τ) :
    ProjectedCopyingReturn Seed pe (ofRegion Seed (productFstBranches (Φ := Φ) A B)) :=
  mem_of_step pe Seed includeStep (fstTerm A B) (.let₂ .var .var) (productFstBranches A B)
    (Paper.TypeCategory.centralCopies_productFst A B) (.fst A B)

include includeStep in
theorem snd_mem (A B : τ) :
    ProjectedCopyingReturn Seed pe (ofRegion Seed (productSndBranches (Φ := Φ) A B)) :=
  mem_of_step pe Seed includeStep (sndTerm A B) (.let₂ .var .var) (productSndBranches A B)
    (Paper.TypeCategory.centralCopies_productSnd A B) (.snd A B)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithProjectionReturnValues
