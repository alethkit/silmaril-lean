module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.CapturedSquare.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.InstructionFree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare

/-! # Ordinary simulation squares with one retained capture -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.CapturedSquare

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open RetainedLet (unpackBody)
open PackedBody (applyPacked)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {X A D B : τ} {Γ : VCtx τ} {L : LCtx τ} {p q r s : Region Φ} {t : Tm Φ}

/-- Destructuring a packed capture and state preserves guarded branches at
every exit of the region. -/
theorem unpackBody_valueBranches (hr : ValueBranches [A, X] r L) :
    ValueBranches [Packed X A] (unpackBody r) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare.unpackBody_valueBranches hr

theorem packedStep_typed (hp : ValueBranches [A, X] p [A, B]) :
    ValueBranches [Packed X A] (packedStep p) [Packed X A, B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare.packedStep_typed hp

theorem packedReturn_typed (ht : Tm.HasType [A, X] t D) :
    ValueBranches [Packed X A] (packedReturn t) [Packed X D] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare.packedReturn_typed ht

/-- Feeding the capture and state pair to a destructuring wrapper recovers
the original typed region. -/
theorem applyPacked_unpackBody (hr : ValueBranches [A, X] r L) :
    Paper.Eqv [A, X] (applyPacked (unpackBody r)) r L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare.applyPacked_unpackBody hr

/-- An ordinary square across packed state interfaces is equivalent to the
captured local square in the original Paper relation. Packing pairs the
capture with feedback payloads and leaves outward payloads alone. -/
theorem packed_ordinary_square_iff (hp : ValueBranches [A, X] p [A, B])
    (hq : ValueBranches [D, X] q [D, B]) (ht : Tm.HasType [A, X] t D) :
    stepArrow (packedStep_typed hp) ≫ coprod.map (𝟙 (ofType B)) (ofRegion (packedReturn_typed ht)) =
        ofRegion (packedReturn_typed ht) ≫ stepArrow (packedStep_typed hq) ↔
      Paper.Eqv [A, X] (p.lsubst (liftLSubstVars (boundLocalMap t)))
        ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) [D, B] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare.packed_ordinary_square_iff hp hq ht

/-- Use a packed ordinary square to instantiate the existing opt-in
instruction-free simulation at the captured context. -/
theorem instructionFreeStep_of_packed_square {entry : Region Φ}
    (he : ValueBranches [X] entry [A, B]) (hp : ValueBranches [A, X] p [A, B])
    (hq : ValueBranches [D, X] q [D, B]) (ht : Tm.HasType [A, X] t D) (pure : InstructionFree t)
    (comm : stepArrow (packedStep_typed hp) ≫ coprod.map (𝟙 (ofType B)) (ofRegion (packedReturn_typed ht)) =
      ofRegion (packedReturn_typed ht) ≫ stepArrow (packedStep_typed hq)) :
    InstructionFreeStep [X] (.cfg entry 1 (fun _ => p))
      (.cfg (entry.lsubst (boundLocalMap t)) 1 (fun _ => q)) [B] :=
  .simulate he hp hq ht pure ((packed_ordinary_square_iff hp hq ht).1 comm)

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.CapturedSquare
