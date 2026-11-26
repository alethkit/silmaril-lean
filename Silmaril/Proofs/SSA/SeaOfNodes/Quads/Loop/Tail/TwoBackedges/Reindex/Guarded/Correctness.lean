module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Proofs

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (Admitted admit)

variable {old new : List (ValueSort Width)} {result : Width}
variable [BankDecidableEq Word (dataPorts old)] [BankDecidableEq Word (dataPorts new)]
variable (order : Registers old new)

theorem admit_reindex (p : Admitted old result) :
    admit (program order p.source) (push order p.facts) = .ok (reindex order p) := by
  unfold admit
  split
  next cert h =>
    have eq : cert = (reindex order p).checked := Except.ok.inj (h.symm.trans (reindex order p).admitted)
    cases eq
    rfl
  next reason h =>
    cases h.symm.trans (reindex order p).admitted

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Guarded.Proofs
