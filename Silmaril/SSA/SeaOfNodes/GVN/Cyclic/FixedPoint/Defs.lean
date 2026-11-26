module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Defs
public import Mathlib.Data.Fintype.Card

/-!
# Fixed-point iteration for cyclic GVN

Iterate the synchronous structural refinement round on the finite typed
producer graph. Stop when the stability checker accepts, or on exhausting
the supplied round budget. The default budget is the number of vertices.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint

open Diamond (Signature ValueSort)

universe u v

variable {n : Nat}

/-- The fine partition can split coarse classes and preserves their separations. -/
def Refines (fine coarse : Partition n) : Prop :=
  ∀ i j, fine i = fine j → coarse i = coarse j

/-- Only labels actually used by vertices contribute to the count. -/
def classCount (p : Partition n) : Nat := (Finset.univ.image p).card

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs : List (ValueSort Data)} {sorts : Fin n → ValueSort Data}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- Perform at most `fuel` splitting rounds, checking stability before each. -/
def run (g : Graph Op inputs sorts) : Nat → Partition n → Partition n
  | 0, p => p
  | fuel + 1, p => if checkStable g p then p else run g fuel (refine g p)

/-- Start from the typed profile seed with a budget of one round per vertex. -/
def normalize (g : Graph Op inputs sorts) : Partition n :=
  run g n (seed g)

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint
