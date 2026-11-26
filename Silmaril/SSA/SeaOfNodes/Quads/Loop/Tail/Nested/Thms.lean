module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Correctness

/-! # The selected input uses exactly the write versions of its parsed path -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested

open SeaOfNodes.Diamond (Model ValueSort)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

/-- Each incoming column gives the entire reaching bank before the merge. -/
theorem Program.merge_bank (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    p.mergeBank m old occurrence = (p.pathQuads occurrence).eval m old :=
  Proofs.merge_bank p m old occurrence

/-- The original source execution enters the merge with the selected
column's bank and exactly the visits remaining after the chosen path. -/
theorem Program.run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) :=
  Proofs.run_to_merge p m old fuel

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested
