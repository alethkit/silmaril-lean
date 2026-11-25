module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs

/-! # Soundness and the guarded unit equation -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem branch_unit_eta {a : Tm Φ} {ℓ : Nat}
    (ha : Tm.BranchValue Γ a Silmaril.unit) (hℓ : At L ℓ (Silmaril.unit : τ)) :
    Eqv Γ (.br ℓ .unit) (.br ℓ a) L := by
  have seed : Eqv [(Silmaril.unit : τ)] (.br 0 (.unit : Tm Φ)) (.br 0 (.var 0)) [Silmaril.unit] :=
    .extra (.br rfl .unit) (.br rfl (.var rfl)) .unit
  have input : ∀ ⦃i A⦄, At [(Silmaril.unit : τ)] i A →
      Tm.BranchValue Γ ((fun _ : Nat => a) i) A := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact ha
    | succ i => simp [At] at hi
  have labels : Ren [(Silmaril.unit : τ)] L (fun _ => ℓ) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact hℓ
    | succ i => simp [At] at hi
  exact (seed.substVars input).renameLabels labels

set_option backward.isDefEq.respectTransparency false in
theorem map_discard_eq_id :
    (projection (τ := τ) (Φ := Φ)).map
      (Paper.TypeCategory.discardArrow (Φ := Φ) (Silmaril.unit : τ)) =
      𝟙 ((projection (τ := τ) (Φ := Φ)).obj (Paper.TypeCategory.ofType Silmaril.unit)) := by
  rw [← (projection (τ := τ) (Φ := Φ)).map_id, ← Paper.TypeCategory.ofRegion_id (Φ := Φ)]
  exact (Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ofRegion_eq_iff Step _ _).2
    (branch_unit_eta (.var (i := 0) rfl) (rfl : At [(Silmaril.unit : τ)] 0 Silmaril.unit))

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

theorem step_denotes (e : Step Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  cases e
  have h : lookup M 0 (rfl : At [(Silmaril.unit : τ)] 0 Silmaril.unit) =
      CartesianMonoidalCategory.toUnit (ctxObj M [(Silmaril.unit : τ)]) ≫ M.unitIso.inv := by
    apply (cancel_mono M.unitIso.hom).mp
    exact Subsingleton.elim _ _
  let hi : At [(Silmaril.unit : τ)] 0 Silmaril.unit := rfl
  refine ⟨_, RegionDenotes.br (h := hi) Denotes.unit, ?_⟩
  simpa only [h] using RegionDenotes.br (J := J) (M := M) (Φ := Φ)
    (h := hi) (Denotes.var (i := 0) hi)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEta
