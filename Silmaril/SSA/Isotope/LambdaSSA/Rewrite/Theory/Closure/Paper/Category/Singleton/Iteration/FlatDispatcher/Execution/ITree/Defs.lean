module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Thms

/-! # Value packing for the weak interaction-tree comparison -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open Semantics.Interaction

variable {α : Type u}

/-- Encode the original exit index and payload into the single outward label. -/
def packedTreeOutput (p : Transfer α) : Transfer α :=
  (0, Region.packedExitValue p.1 p.2)

/-- Encode an original block index and argument into the single feedback label. -/
def packedTreeInput {blocks : Nat} (p : BlockInput α blocks) : BlockInput α 1 :=
  (0, Region.packedExitValue p.1.val p.2)

/-- Label zero feeds back and label one leaves the literal packed CFG. -/
def packedTreeTransfer (blocks : Nat) (p : Transfer α) : Transfer α :=
  Sum.elim (fun out => (1, (packedTreeOutput out).2))
    (fun next => (0, (packedTreeInput next).2)) (splitTransfer blocks p)

end Silmaril.Isotope.LambdaSSA.FiniteCFG
