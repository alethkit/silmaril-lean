module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetOperand

/-! # Representative-changing replay through a constructor state map -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open Paper.TypeCategory (ofType ofRegion sumIso)
open Extension.Singleton (projection projectStep iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {Φ : Type v}

/-- Variable substitution preserves the rewrite site and commutes with moving the let. -/
theorem Site.move_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    site.move (r.substVars θ) = (site.move r).map (·.substVars θ) :=
  EntryLetOperand.move_substVars site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

/-- A successful move on a substituted region factors through the same move
on the original guarded region, with its original typing context and exits. -/
theorem Site.move_pullback (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (θ : Nat → Tm Φ)
    (hm : site.move (r.substVars θ) = some s) :
    ∃ q, site.move r = some q ∧ s = q.substVars θ ∧
      ValueBranches Γ q L ∧ Eqv Γ r q L :=
  EntryLetOperand.move_pullback site hr θ hm

/-- Replay the given sites before substitution. At every move the
pulled-back region substitutes to exactly the next composite. -/
theorem Site.moveAll_pullback (sites : List Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (θ : Nat → Tm Φ)
    (hm : Site.moveAll sites (r.substVars θ) = some s) :
    ∃ q, Site.moveAll sites r = some q ∧ s = q.substVars θ ∧
      ValueBranches Γ q L ∧ Eqv Γ r q L :=
  EntryLetOperand.moveAll_pullback sites hr θ hm

variable {A D B : τ} {a : Tm Φ} {r s : Region Φ}

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (τ := τ) (Φ := Φ)

/-- Precomposition with a constructor return substitutes that constructor
for the target's input. -/
theorem ofRegion_comp_constructor {C : τ} (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [C])
    (hs : ValueBranches [A] (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) [C]) :
    ofRegion (.br (ℓ := 0) rfl ha) ≫ ofRegion hr = ofRegion hs :=
  EntryLetOperand.comp_constructor ha hr hs

/-- If the finite forward chain on the written target composite ends at a
standard Paper representative of the source composite, replay it in the
target operand. The replacement has the same corrected class and gives
a native commuting square. -/
theorem repairTargetMoves (sites : List Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : Site.moveAll sites (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    ∃ g : Obj D ⟶ Obj B ⨿ Obj D,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso B D).hom) ∧
      f ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g :=
  EntryLetOperand.repairTargetMoves sites ha hr f hs hm comm

/-- Replay a finite chain, then apply standard Paper constructor uniformity. -/
theorem uniformity_of_target_moves (sites : List Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : Site.moveAll sites (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    iterateChosen Seed (projectStep Seed f) =
      (projection Seed).map (ofRegion (.br (ℓ := 0) rfl ha)) ≫
        iterateChosen Seed (projectStep Seed (ofRegion hr ≫ (sumIso B D).hom)) :=
  EntryLetOperand.uniformity_of_target_moves sites ha hr f hs hm comm

private theorem Site.moveAll_singleton (site : Site) (r : Region Φ) :
    Site.moveAll [site] r = site.move r := by
  change (site.move r >>= some) = site.move r
  cases site.move r <;> rfl

/-- If one contextual entry-let move on the written target composite
produces a representative of the source composite, the move can be made
in the target operand. The new target represents the same corrected step
and commutes with the written source in standard Paper. -/
theorem repairTarget (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : site.move (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    ∃ g : Obj D ⟶ Obj B ⨿ Obj D,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso B D).hom) ∧
      f ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g :=
  repairTargetMoves [site] ha hr f hs (by rwa [Site.moveAll_singleton]) comm

/-- The repaired square gives iteration equality in the corrected quotient
by standard Paper constructor uniformity. -/
theorem uniformity_of_target_move (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : site.move (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    iterateChosen Seed (projectStep Seed f) =
      (projection Seed).map (ofRegion (.br (ℓ := 0) rfl ha)) ≫
        iterateChosen Seed (projectStep Seed (ofRegion hr ≫ (sumIso B D).hom)) :=
  uniformity_of_target_moves [site] ha hr f hs (by rwa [Site.moveAll_singleton]) comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
