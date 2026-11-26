module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms.Returns

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs results : List (ValueSort Data)} {sigs : List (List (Ty Data))}

theorem Graph.returns_iff_denote (m : Model.{u,v,w} Op) (g : Graph Op inputs sigs results)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : Tuple (Val m.value) (dataPorts results)) :
    g.Returns m entry result ↔ g.denote m entry = result :=
  Proofs.SSA.SeaOfNodes.Diamond.Arms.returns_iff_denote m g entry result

end Silmaril.SSA.SeaOfNodes.Diamond.Arms
