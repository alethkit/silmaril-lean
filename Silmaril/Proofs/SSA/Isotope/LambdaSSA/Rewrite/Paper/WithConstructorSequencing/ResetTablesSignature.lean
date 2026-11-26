module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Observation.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.ResetTables

/-! # Observing fixed resets over free simple types -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesSignature

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ResetTables
open ResetTables (reset_then_inl reset_then_inr)
open Paper.BoundSimulation.Obstruction.PairSequencing (reset_ne_forward reset_left_ne_right)

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]
  {P : Ty α} {w : Tm Φ} (hw : Tm.BranchValue [] w P)

set_option backward.isDefEq.respectTransparency false

theorem separatesActions : SeparatesActions hw := by
  intro eq
  change projection.map (ofRegion (.br (ℓ := 0) rfl (resetValue hw))) =
    projection.map (𝟙 (ofType P)) at eq
  rw [← ofRegion_id P] at eq
  exact reset_ne_forward hw ((Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (.br (ℓ := 0) rfl (resetValue hw)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))).mp eq)

theorem separatesResetTags : SeparatesResetTags hw := by
  intro eq
  change projection.map (action hw .literal ≫ (coprod.inl : ofType P ⟶ ofType P ⨿ ofType P)) =
    projection.map (action hw .literal ≫ coprod.inr) at eq
  simp only [← sumCofan_inl_sumIso_hom P P, ← sumCofan_inr_sumIso_hom P P,
    ← Category.assoc, Functor.map_comp] at eq
  have tags := (cancel_mono (projection.map (sumIso P P).hom)).mp eq
  rw [← projection.map_comp, ← projection.map_comp, reset_then_inl, reset_then_inr] at tags
  exact reset_left_ne_right hw ((Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (.br (ℓ := 0) rfl (.inl (B := P) (resetValue hw)))
    (.br (ℓ := 0) rfl (.inr (A := P) (resetValue hw)))).mp tags)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesSignature
