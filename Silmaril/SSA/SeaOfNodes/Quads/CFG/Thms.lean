module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Correctness

/-! # Exact placement and selected-edge bank agreement for acyclic quads -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG

open RVSDG (Port)
open Diamond (Ty ValueSort Signature Model dataPorts)

universe u v w
variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {n : Nat}

/-- A Φ is allocated exactly when some incoming version differs from the
first version of the same register. The test ranges over the full bank. -/
theorem Graph.header_phi_iff {t : Ty Data} (prior : Graph Op regs n) (preds : Predecessors n)
    (p : Port (dataPorts regs) t) :
    (prior.header preds).get p = none ↔
      ∃ pred ∈ preds.rest, (prior.versions pred).get p ≠ (prior.versions preds.first).get p :=
  Proofs.header_phi_iff prior preds p

/-- Reading the compiled outgoing map after any checked path recovers the
complete final bank of ordered quad execution. All those versions are defined. -/
theorem Path.versions_agree {graph : Graph Op regs n} {i : Fin n} (path : Path graph i)
    (m : Model.{u, v, w} Op) (input : Bank m regs) :
    ∃ values, path.values m input = some values ∧
      readBank (dataPorts regs) (values.read (graph.versions i)) = some (path.eval m input) :=
  Proofs.path_bank path m input

/-- On any incoming occurrence, the selected column and the successor's
merged inputs both read exactly the predecessor's final source bank. -/
theorem Graph.edge_agrees (prior : Graph Op regs n) (preds : Predecessors n)
    (occurrence : Fin (preds.rest.length + 1)) (path : Path prior (preds.get occurrence))
    (m : Model.{u, v, w} Op) (input : Bank m regs) :
    ∃ values, path.values m input = some values ∧
      readBank (dataPorts regs) (values.read (prior.column preds occurrence)) =
        some (path.eval m input) ∧
      readBank (dataPorts regs) ((prior.header preds).read values
        (values.read (prior.column preds occurrence))) = some (path.eval m input) :=
  Proofs.edge_bank prior preds occurrence path m input

end Silmaril.SSA.SeaOfNodes.Quads.CFG
