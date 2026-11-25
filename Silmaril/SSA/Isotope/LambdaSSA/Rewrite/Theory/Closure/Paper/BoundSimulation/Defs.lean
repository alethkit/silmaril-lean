module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs

/-! # Guarded state changes at a local feedback label -/

public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

/-- Evaluate a new state once at local label zero and forward all outward labels. -/
@[expose] def boundLocalMap {Φ : Type v} (t : Tm Φ) : Nat → Region Φ
  | 0 => (Region.br 0 t).bindBranchArguments
  | i + 1 => .br (i + 1) (.var 0)

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
