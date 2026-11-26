module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

/-! # Shared unequal-arm source fixture -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Example

open Blocks.Example

-- Entry 4, header 2, true arm 5 → 6, false arm 0, merge 3, latch 1.
def source (trueNext : Fin 7) : Source Arithmetic regs num 7 :=
  fun i =>
    if i = 4 then
      ⟨[⟨_, _, x, .copy, .cons stride .nil⟩], .transfer (.jump 2)⟩
    else if i = 2 then
      ⟨[⟨_, _, again, .positive, .cons x .nil⟩], .branch again (.jump 5) (.jump 0)⟩
    else if i = 5 then
      ⟨[⟨_, _, y, .add, .cons y (.cons stride .nil)⟩], .transfer (.jump trueNext)⟩
    else if i = 6 then
      ⟨[⟨_, _, y, .add, .cons y (.cons stride .nil)⟩, ⟨_, _, x, .copy, .cons saved .nil⟩],
        .transfer (.jump 3)⟩
    else if i = 0 then
      ⟨[⟨_, _, y, .add, .cons y (.cons y .nil)⟩, ⟨_, _, x, .copy, .cons stride .nil⟩],
        .transfer (.jump 3)⟩
    else if i = 3 then
      ⟨[⟨_, _, y, .copy, .cons y .nil⟩], .transfer (.jump 1)⟩
    else
      ⟨[⟨_, _, counter, .pred, .cons counter .nil⟩, ⟨_, _, again, .positive, .cons counter .nil⟩],
        .branch again (.jump 2) (.ret y)⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Example
