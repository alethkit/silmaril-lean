module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Defs

/-! # A cycle with two distinct constructor assignments -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple.Example

open UnitSumSquare.Cycles.Mixed.MergeCycle (result source target tags sourceRows targetRows)
open scoped Paper.BoundSimulation.Obstruction

abbrev P : Ty Empty := .coprod .unit .unit

def left : ClosedValue Empty P := ⟨.inl .unit, .inl .unit⟩
def right : ClosedValue Empty P := ⟨.inr .unit, .inr .unit⟩

/-- The alternating cycle and the terminating path each use both assignments. -/
def sourceSteps : source.Row → OutputCode (ClosedValue Empty P) result source
  | i@(.inl (.inl ())) => ⟨sourceRows i, some left⟩
  | i@(.inr (.inl ())) => ⟨sourceRows i, some left⟩
  | i => ⟨sourceRows i, some right⟩

/-- The folded self-loop resets to the right value. The exiting path is retained. -/
def targetSteps : target.Row → OutputCode (ClosedValue Empty P) result target
  | i@(.inr (.inl ())) => ⟨targetRows i, some left⟩
  | i => ⟨targetRows i, some right⟩

/-- Merge the two cyclic rows while resetting. Forward the payload of exiting rows. -/
def stateRows : source.Row → StateCode (ClosedValue Empty P) target
  | i@(.inl _) => ⟨tags i, some right⟩
  | i => ⟨tags i, none⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables.Multiple.Example
