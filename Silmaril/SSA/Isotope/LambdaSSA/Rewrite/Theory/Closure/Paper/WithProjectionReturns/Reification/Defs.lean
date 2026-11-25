module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Defs

/-! # Lowered projection producers for guarded LambdaSSA -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion)

universe v
variable {Φ : Type v}

/-- Evaluate the first expression, then the second in the original input context. -/
def pairTerm (a b : Tm Φ) : Tm Φ :=
  .let₁ a (.let₁ (b.rename Nat.succ) (.pair (.var 1) (.var 0)))

/-- Rebuild a packed record by evaluating its first and second projections. -/
def rebuildPair : Tm Φ := pairTerm (.let₂ (.var 0) (.var 1)) (.let₂ (.var 0) (.var 0))

/-- Evaluate the two projections in reverse order to produce the swapped record. -/
def swapPair : Tm Φ := pairTerm (.let₂ (.var 0) (.var 0)) (.let₂ (.var 0) (.var 1))

/-- Run a guarded region after rebuilding its packed singleton input. -/
def afterRebuild (p : Region Φ) : Region Φ :=
  compLSubst (fun _ => returnRegion rebuildPair) (fun _ => p) 0

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturns.Reification
