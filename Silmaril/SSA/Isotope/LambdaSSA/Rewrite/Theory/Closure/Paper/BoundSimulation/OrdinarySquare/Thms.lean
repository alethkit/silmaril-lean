module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundOrdinarySquare

/-! # Transport an ordinary commuting square to the typed feedback labels -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open ContinuationContext (single)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {A B D : τ} {t : Tm Φ} {p q : Region Φ}

/-- Every chosen-sum step has a guarded representative with repeat at label zero. -/
theorem exists_stepArrow (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A) :
    ∃ p : Region Φ, ∃ hp : ValueBranches [A] p [A, B], f = stepArrow hp :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundOrdinarySquare.exists_stepArrow f

/-- Chosen iteration of the packed step runs the corresponding literal CFG. -/
theorem iterate_stepArrow (hp : ValueBranches [A] p [A, B]) :
    iterate (stepArrow hp) = ofRegion (stepFeedback_typed hp) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundOrdinarySquare.iterate_stepArrow hp

/-- A guarded singleton return changes the local state. This permits a
state change that packages its retained input along with the new state. -/
theorem ordinary_square_of_region_iff {r : Region Φ} (hp : ValueBranches [A] p [A, B])
    (hq : ValueBranches [D] q [D, B]) (hr : ValueBranches [A] r [D]) :
    stepArrow hp ≫ coprod.map (𝟙 (ofType B)) (ofRegion hr) =
        ofRegion hr ≫ stepArrow hq ↔
      Paper.Eqv [A] (p.lsubst (liftLSubstVars (regionLocalMap r)))
        (r.lsubst (liftLSubstVars (fun _ => q))) [D, B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundOrdinarySquare.ordinary_square_of_region_iff hp hq hr

/-- The ordinary coproduct square for guarded representatives is exactly the
bound local square at labels zero (repeat) and one (outward). Purity is needed
when applying the feedback rule, while this transport only needs exact typing. -/
theorem ordinary_square_iff (hp : ValueBranches [A] p [A, B])
    (hq : ValueBranches [D] q [D, B]) (ht : Tm.HasType [A] t D) :
    stepArrow hp ≫ coprod.map (𝟙 (ofType B)) (boundReturn ht) =
        boundReturn ht ≫ stepArrow hq ↔
      Paper.Eqv [A] (p.lsubst (liftLSubstVars (boundLocalMap t)))
        ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) [D, B] :=
  ordinary_square_of_region_iff hp hq (Paper.RetainedLet.returnOnce_typed ht)

/-- A closed entry and a certified instruction-free state change turn the
ordinary commuting square into a typed feedback step. -/
theorem instructionFreeStep_of_ordinary_square {entry : Region Φ}
    (he : ValueBranches [] entry [A, B]) (hp : ValueBranches [A] p [A, B])
    (hq : ValueBranches [D] q [D, B]) (ht : Tm.HasType [A] t D) (pure : InstructionFree t)
    (comm : stepArrow hp ≫ coprod.map (𝟙 (ofType B)) (boundReturn ht) =
      boundReturn ht ≫ stepArrow hq) :
    InstructionFreeStep [] (.cfg entry 1 (fun _ => p))
      (.cfg (entry.lsubst (boundLocalMap t)) 1 (fun _ => q)) [B] :=
  .simulate he hp hq ht pure ((ordinary_square_iff hp hq ht).1 comm)

/-- To use the recursively lowered return as the state change, the exact
comparison is the Paper equation between its single-exit representatives. -/
theorem returnTerm_eq_boundReturn_iff (ht : Tm.HasType [A] t D) :
    returnTerm ht = boundReturn ht ↔
      Paper.Eqv [A] (CfgEta.TypeCategory.returnRegion t) (Paper.RetainedLet.returnOnce t) [D] :=
  ofRegion_eq_iff _ _

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
