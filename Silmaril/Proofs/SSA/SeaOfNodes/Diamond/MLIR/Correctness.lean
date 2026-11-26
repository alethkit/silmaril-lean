module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms
public import Silmaril.SSA.RVSDG.MLIR.Graph.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Proofs

open RVSDG (Port Tuple)

variable {Data : Type} {Op : Diamond.Signature.{0, 0} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}

theorem returns_iff_denote (m : Model.{0, 0, 0} Op) (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    g.Returns m entry result ↔ denote m g entry = result := by
  have h := RVSDG.MLIR.Graph.denote_lower (P := source Op) m.toRVSDG g.lower entry
  change Tuple.cons (F := m.toRVSDG.Val) (t := .value out) (denote m g entry) Tuple.nil =
    g.lower.run m.toRVSDG entry at h
  rw [g.lower_returns_iff m entry result, ← h]
  exact ⟨fun eq => congrArg (fun xs => Tuple.get xs Port.head) eq,
    fun eq => congrArg (fun value => Tuple.cons value Tuple.nil) eq⟩

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Proofs
