module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit

/-! # Exact block and retained loop denotations for captured repeat/exit -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory CapturedRecurExit
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

/-- The chosen denotation of the packed block has the two expected rows.
The proof inverts its denotation graph at the exact typing. -/
theorem denoteBlock_apply (c s : Bits) :
    (denoteSingletonRegion J M blockBound.hasType).of (c, s) = Sum.inl (blockValue c s) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit.denoteBlock_apply c s

/-- The retained block preserves the extra capture through its two product comparisons. -/
theorem retainedBlock_apply (outer c s : Bits) :
    (J.map (M.productIso Flag Carry).hom ≫
      retainLeft J (R := M.obj Flag) (denoteSingletonRegion J M blockBound.hasType) ≫
      J.map (M.productIso Flag Exit).inv).of (outer, (c, s)) =
        (Sum.inl (outer, blockValue c s) : MaybeT (Bits × obj Exit)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit.retainedBlock_apply outer c s

/-- The actual carried step updates the state on repeat and retains the capture on return. -/
theorem exactStep_apply (c s : Bits) :
    exactStep.of (stateInput c s) =
      (Sum.inl (match s with
        | .inl _ => Sum.inr (stateInput c (.inr PUnit.unit))
        | .inr _ => Sum.inl (stateInput c c)) : MaybeT (Carried ⊕ Carried)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit.exactStep_apply c s

/-- Iteration on the actual contextual step returns the capture from either starting state. -/
theorem iterate_apply (c s : Bits) :
    (CategoryTheory.iterate actualStep).of (stateInput c s) = (Sum.inl (stateInput c c) : MaybeT Carried) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit.iterate_apply c s

/-- In packed coordinates the same retained iterator returns the pair of captured values. -/
theorem iterate_repacked_apply (c s : Bits) :
    ((J).map (carriedIso M Flag Flag).inv ≫
      CategoryTheory.iterate actualStep ≫
      (J).map (carriedIso M Flag Flag).hom).of (c, s) =
        (Sum.inl (c, c) : MaybeT (Bits × Bits)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit.iterate_repacked_apply c s

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit
