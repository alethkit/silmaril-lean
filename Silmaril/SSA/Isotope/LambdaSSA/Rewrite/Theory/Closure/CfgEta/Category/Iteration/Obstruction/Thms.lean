module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Obstruction.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CategorySequencingWitness

/-! # The native fixpoint witness becomes equal in the CFG η quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.SequencingWitness

open CategoryTheory
open Region.SequencingObstruction (Instruction)

theorem native_distinct : loop ≠ unrolled :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.sequencingWitness_native_distinct

theorem enlarged_equal : fromNative.map loop = fromNative.map unrolled :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.sequencingWitness_enlarged_equal

theorem fromNative_not_faithful :
    ¬ (fromNative (Φ := Instruction) (Γ := ([] : VCtx (Ty Empty)))).Faithful :=
  fun h => native_distinct (h.map_injective enlarged_equal)

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.SequencingWitness
