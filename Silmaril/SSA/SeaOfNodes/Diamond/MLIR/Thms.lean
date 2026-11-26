module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.MLIR.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR

open RVSDG (Tuple)

variable {Data : Type} {Op : Diamond.Signature.{0, 0} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}

/-- A finite source return has exactly the value of the lowered scoped MLIR
block, with the source model interpreted in the project dialect. -/
theorem returns_iff_denote (m : Model.{0, 0, 0} Op) (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    g.Returns m entry result ↔ denote m g entry = result :=
  Proofs.returns_iff_denote m g entry result

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR
