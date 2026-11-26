module

import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef

open RVSDG (Tuple)
open RVSDG.MLIR.Graph.Feedback (Code)
open Silmaril.MLIR.MemRef (Buffer Op Ty)

private abbrev args : List ValueSort := [.address, .address]

private def copyThenRead : Graph args :=
  .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg (.tail .head)) (.output 0 .head)
      (.load (.latest 1) (.arg (.tail .head))
        (.ret (.latest 1) (.output 0 .head))))

private def readSource : Graph args :=
  .load (.latest 0) (.arg .head) (.ret (.latest 0) (.output 0 .head))

private def inputs : Tuple (Val 3) args := .cons (0 : Address 3) (.cons (1 : Address 3) .nil)

private def initial : Buffer 3 :=
  ⟨fun i => if i = 0 then 11 else if i = 1 then 22 else 99⟩

private def readback (result : Word × Buffer 3) : Word × Word × Word × Word :=
  (result.1, result.2.cell 0, result.2.cell 1, result.2.cell 2)

private def operationNames {scope : List (List (Ty 3))} {outs : List (Ty 3)} :
    Code (Op 3) scope outs → List String
  | .prim op _ rest => op.name :: operationNames rest
  | .yield _ | .choose .. | .feedback .. => []

example : operationNames (lower 3 copyThenRead).val = ["memref.load", "memref.store", "memref.load"] := rfl

-- The second load sees the preceding store. The unrelated cell is unchanged.
#guard readback (observe copyThenRead inputs initial) == (11, 11, 11, 99)

-- With the store absent, the same word is returned and cell one differs.
#guard readback (observe readSource inputs initial) == (11, 11, 22, 99)

end Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef
