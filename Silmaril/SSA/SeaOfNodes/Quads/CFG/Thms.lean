module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Correctness

/-! # Exact placement and selected-edge bank agreement for acyclic quads -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG

open RVSDG (Locals Port Tuple Wires)
open Diamond (Ty ValueSort Signature Model Val dataPorts)
open Join (Block)

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

/-- Reusing a header definition means it is the definition on every incoming occurrence. -/
theorem Graph.header_reuse {t : Ty Data} (prior : Graph Op regs n) (preds : Predecessors n)
    (edge : Fin (preds.rest.length + 1)) (p : Port (dataPorts regs) t)
    (version : Version n) (same : (prior.header preds).get p = some version) :
    (prior.column preds edge).get p = version :=
  Proofs.selected_version prior preds edge p version same

/-- The reusable local producer transfer reads the final ordered source bank. -/
theorem compileBlock_read {args : List (Ty Data)} {past : List (List (Ty Data))}
    (block : Block Op regs) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (compileBlock block current).outgoing.read entry
        ((compileBlock block current).flow.eval m entry locals) =
      block.eval m (current.read entry locals) :=
  Proofs.compiled_read block m entry locals current

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
