module

public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Equality.Addresses

/-! # Faithfulness of typed address and generator codes -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Equality

universe u v
variable {Ty : Type u} {args users : Ports Ty} {past : List (Ports Ty)}

theorem addresses_injective (x y : Wires args past users) (h : x.addresses = y.addresses) : x = y :=
  Proofs.addresses_injective x y h

variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {ins outs : Ports (PortType V S)}

theorem kind_injective (code : OpcodeCode Op) (x y : Kind Op ins outs)
    (h : kindCode code x = kindCode code y) : x = y :=
  Proofs.kind_injective code x y h

end Silmaril.SSA.RVSDG.NestedTheta.Equality
