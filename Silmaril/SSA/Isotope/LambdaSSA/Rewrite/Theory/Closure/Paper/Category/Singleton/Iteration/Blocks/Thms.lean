module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BlockElimination

/-! # Elimination of feedback over packed block interfaces -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ
local notation "iter" => Paper.TypeCategory.iterate

open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

@[reassoc (attr := simp)] theorem inl_blockCopair {A D : τ} {Y : Comp}
    (f : ofType A ⟶ Y) (g : ofType D ⟶ Y) : (sumCofan A D).inl ≫ blockCopair f g = f :=
  BlockElimination.inl_blockCopair f g

@[reassoc (attr := simp)] theorem inr_blockCopair {A D : τ} {Y : Comp}
    (f : ofType A ⟶ Y) (g : ofType D ⟶ Y) : (sumCofan A D).inr ≫ blockCopair f g = g :=
  BlockElimination.inr_blockCopair f g

/-- Splitting and then joining the recurrence ports preserves the original packed exit. -/
theorem split_join (A D : τ) (Y : Comp) :
    splitBlockExits A D Y ≫ joinBlockExits A D Y = 𝟙 _ :=
  BlockElimination.split_join A D Y

/-- Eliminate the right block first. The left block's exits stay exposed during
the inner iteration and are fed back during the outer iteration. -/
theorem iterate_join_blocks (A D : τ) (Y : Comp)
    (f : ofType A ⟶ (Y ⨿ ofType A) ⨿ ofType D)
    (g : ofType D ⟶ (Y ⨿ ofType A) ⨿ ofType D) :
    let right := iter g
    let left := iter (f ≫ coprod.desc (𝟙 (Y ⨿ ofType A)) right)
    iter (blockCopair f g ≫ joinBlockExits A D Y) =
      blockCopair left (right ≫ coprod.desc (𝟙 Y) left) :=
  BlockElimination.iterate_join_blocks A D Y f g

/-- Feedback on a packed finite block interface agrees with tail-first elimination.
The step is any Paper singleton arrow, including one that branches on payloads
or executes instructions. The proof uses constructor uniformity on the block
injections and the existing fixpoint, naturality, and codiagonal laws. -/
theorem eliminateBlocks_eq_iterate (R : LCtx τ) {Y : Comp}
    (step : ofType (packedExitType R) ⟶ Y ⨿ ofType (packedExitType R)) :
    eliminateBlocks R step = iter step :=
  BlockElimination.eliminateBlocks_eq_iterate R step

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
