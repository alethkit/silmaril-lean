module

public import Silmaril.SSA.SeaOfNodes.GVN.Discovery.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Discovery

open Diamond (Dataflow Signature Ty ValueSort)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}
variable [DecidableEq (ValueSort Data)]

/-- The enumeration includes every strictly earlier producer of the same result sort. -/
theorem mem_earlier_iff (candidate representative : Producer flow out) :
    representative ∈ earlier candidate ↔ position representative < position candidate :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery.mem_earlier_iff candidate representative

variable [∀ ins out, DecidableEq (Op ins out)]

/-- A reported representative is accepted by the existing structural-key checker. -/
theorem findRepresentative?_sound (candidate representative : Producer flow out)
    (found : findRepresentative? candidate = some representative) :
    checkRepresentative candidate representative = true :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery.find_sound candidate representative found

/-- Search failure excludes every checker-accepted representative in this table. -/
theorem findRepresentative?_eq_none_iff (candidate : Producer flow out) :
    findRepresentative? candidate = none ↔
      ∀ representative : Producer flow out, checkRepresentative candidate representative = false :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery.find_none_iff candidate

end Silmaril.SSA.SeaOfNodes.GVN.Discovery
