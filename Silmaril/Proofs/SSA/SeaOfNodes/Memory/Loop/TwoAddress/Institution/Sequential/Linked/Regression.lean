module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked

open CategoryTheory
open RVSDG (Port Tuple)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Fixture

private abbrev extra := [ValueSort.address, .address, .word]
private abbrev combined : EntrySignature := ⟨captures.args ++ extra⟩

private def prefixPort {sort : ValueSort} :
    {args : List ValueSort} → Port args sort → Port (args ++ extra) sort
  | _, .head => .head
  | _, .tail port => .tail (prefixPort port)

private def first : Graph combined.args := mapGraph (P := captures) (Q := combined) ⟨prefixPort⟩ graph

private def firstRight : Port combined.args .address := .tail (.tail (.tail (.tail .head)))
private def secondRight : Port combined.args .address := .tail (.tail (.tail (.tail (.tail .head))))
private def rightStore : Port combined.args .word := .tail (.tail (.tail (.tail (.tail (.tail .head)))))

private def wiring : Boundary.Wiring combined.args captures.args :=
  .forward firstRight (.forward secondRight (.word fun
    | .head => rightStore
    | .tail impossible => nomatch impossible))

private abbrev inputs : Tuple (Val 6) combined.args :=
  SeaOfNodes.Loop.appendTuple
    (.cons (right 0) (.cons (right 1) (.cons (22 : Word) .nil)) : Tuple (Val 6) extra)
    (CellEmbedding.input left model.input)

example (word : Word) : wiring.select word inputs = CellEmbedding.input right (next word) := rfl

private def run (fuel : Nat) : Option (Word × Word × List Word) :=
  ((lower first graph wiring).run (thetaRuntime 6) fuel (encodeInput initial inputs)).map fun raw =>
    let (word, nextWord, heap) := (resultCodec 6).symm raw
    (word, nextWord, (List.finRange 6).map heap)

-- Two actual θ vertices share a live heap in one compiled graph. Each
-- requires its initial activation and one backedge on these inputs.
#guard (run 1).isNone
#guard run 2 == some (3, 3, [11, 73, 11, 22, 91, 22])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked
