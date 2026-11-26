module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF

open Fixture
open Silmaril.MLIR.MemRef (Buffer)

private def summarize (result : Option (Word × Buffer 3)) : Option (Word × Word × Word × Word) :=
  result.map fun (word, final) => (word, final.cell 0, final.cell 1, final.cell 2)

-- The entry edge, first header, and exit all execute at zero backedges.
#guard summarize (run shift input 0 ⟨initial 0⟩) == some (0, 2, 0, 99)

private def oneBackedge : Buffer 3 :=
  ⟨fun cell => if cell = headCell then 1 else if cell = tailCell then 0 else 99⟩

-- The first header replaces 1 with 0 and takes its self edge. The next
-- header reads 0 from that buffer and takes the edge to the exit.
#guard (run shift input 0 oneBackedge).isNone
#guard summarize (run shift input 1 oneBackedge) == some (0, 0, 0, 99)
#guard summarize (run shift input 2 oneBackedge) == some (0, 0, 0, 99)

-- The native shift fixture needs two backedges with its original tail cell.
#guard (run shift input 1 ⟨initial 1⟩).isNone
#guard summarize (run shift input 2 ⟨initial 1⟩) == some (0, 0, 0, 99)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF
