module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms

/-! # Denotations of the guarded projection return steps -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithProjectionReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion_typed)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
private theorem projection_denotation {A B D : τ} {i : Nat} (h : At [B, A, product A B] i D) :
    denoteRegion J M (returnRegion_typed (.let₂ (.var (i := 0) rfl) (.var h) :
      Tm.HasType [product A B] (.let₂ (.var 0) (.var i) : Tm Φ) D)).hasType =
    denoteRegion J M (.let₂ (.var (i := 0) rfl)
      (.br (Φ := Φ) (ℓ := 0) (L := [D]) rfl (.var h))) := by
  let p : Tm.HasType [product A B] (.var 0 : Tm Φ) (product A B) := .var rfl
  let c : Tm.HasType [B, A, product A B] (.var i : Tm Φ) D := .var h
  have exit : At [D] 0 D := rfl
  change denoteRegion J M (.let₁ (.let₂ p c) (.br exit (.var (i := 0) rfl))) = _
  rw [← denote_let₂_boundReturn_fusion J M exit p c]
  have beta : RewriteEquiv [B, A, product A B] (.let₁ (.var i) (.br 0 (.var 0)))
      (.br 0 (.var i) : Region Φ) [D] :=
    .letBr (.var h) (.var (i := 0) rfl) exit
  exact (RewriteEquiv.let₂ p beta).sound J M _ _

theorem step_sound (e : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  cases e with
  | fst A B => exact projection_denotation J M (rfl : At [B, A, product A B] 1 A)
  | snd A B => exact projection_denotation J M (rfl : At [B, A, product A B] 0 B)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithProjectionReturns
