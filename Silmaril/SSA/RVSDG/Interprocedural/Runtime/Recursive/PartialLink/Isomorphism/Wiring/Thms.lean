module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ids : GlobalRel} {rename : Nat → Nat}
variable {args ports : Ports (Ty V S)} {pastL pastR : List (Ports (Ty V S))}

/-- Locals agree at corresponding typed producer ports. A binding with no
outputs contributes no observable port to this relation. -/
def LocalsRelated (m : Machine.{u, v, w} Op) (ids : GlobalRel) (rename : Nat → Nat)
    (left : Locals m.Val pastL) (right : Locals m.Val pastR) : Prop :=
  Proofs.LocalsRelated m ids rename left right

namespace LocalsRelated

theorem empty : LocalsRelated m ids rename (pastL := []) (pastR := []) PUnit.unit PUnit.unit :=
  Proofs.LocalsRelated.empty

variable {left : Locals m.Val pastL} {right : Locals m.Val pastR}

theorem emptyLeft (related : LocalsRelated m ids rename left right) :
    LocalsRelated m ids rename (left.snoc (.nil : Tuple m.Val [])) right :=
  Proofs.LocalsRelated.emptyLeft related

theorem emptyRight (related : LocalsRelated m ids rename left right) :
    LocalsRelated m ids rename left (right.snoc (.nil : Tuple m.Val [])) :=
  Proofs.LocalsRelated.emptyRight related

theorem snoc {nextL nextR : Tuple m.Val ports} (injective : Function.Injective rename)
    (position : rename pastL.length = pastR.length) (related : LocalsRelated m ids rename left right)
    (outputs : TupleRelated m ids nextL nextR) :
    LocalsRelated m ids rename (left.snoc nextL) (right.snoc nextR) :=
  Proofs.LocalsRelated.snoc injective position related outputs

end LocalsRelated

theorem readWires_related {inputsL inputsR : Tuple m.Val args}
    {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR}
    (inputs : TupleRelated m ids inputsL inputsR) (locals : LocalsRelated m ids rename localsL localsR)
    (left : Wires args pastL ports) (right : Wires args pastR ports)
    (edges : left.addresses.map (Address.rename rename) = right.addresses) :
    TupleRelated m ids (left.read inputsL localsL) (right.read inputsR localsR) :=
  Proofs.read_related inputs locals left right edges

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism
