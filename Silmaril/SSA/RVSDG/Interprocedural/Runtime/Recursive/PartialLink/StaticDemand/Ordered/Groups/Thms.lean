module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Correct

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered.Prefix (Row memberRow)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {actions : Actions m σ} {earlier later : MemberSummaries V S}
variable {imports exports : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

theorem Dispatch.combined_transport (old : Dispatch actions earlier) (new : Dispatch actions later) :
    ∀ i, DispatchAt actions ((append earlier later).at i) ((old.left.combine new.left) i)
      ((old.right.combine new.right) i) :=
  Groups.Proofs.combine old new

@[expose] def Dispatch.combine (old : Dispatch actions earlier) (new : Dispatch actions later) :
    Dispatch actions (append earlier later) :=
  ⟨old.left.combine new.left, old.right.combine new.right, old.combined_transport new⟩

theorem Known.oldSlot {left : Guard m earlier} (right : Guard m later)
    {ty : Ty V S} {value : m.Val ty} :
    Known left value → Known (left.combine right) value :=
  Groups.Proofs.oldKnown right

theorem Known.newSlot (left : Guard m earlier) {right : Guard m later}
    {ty : Ty V S} {value : m.Val ty} :
    Known right value → Known (left.combine right) value :=
  Groups.Proofs.newKnown left

/-- Add the exact linked members of an independently checked group to one
physical row. Its demand slots follow the earlier dispatch slots. -/
@[expose] def GroupBinding.checkedRow (binding : GroupBinding Op later imports past)
    (guard : Guard m earlier) (captured : Tuple m.Val binding.family.context) :
    Row (Known (guard.combine (binding.family.guard captured))) (binding.family.references captured) :=
  memberRow later.members (binding.family.memberValue captured) fun i =>
    Known.newSlot guard
      (Known.callable (guard := binding.family.guard captured) i _ (binding.family.capturedAt captured i) ⟨rfl, rfl⟩)

theorem GroupBinding.link_step (binding : GroupBinding Op later imports past)
    (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val imports)
    (locals : Locals m.Val past) (rest : ModuleTerm Op imports (past ++ [memberPorts later.members]) sigs exports)
    (store : σ) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals (.bind (.phi binding.term) rest) store =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs (binding.locals inputs locals) rest store :=
  Groups.Proofs.link_step binding actions unitId inputs locals rest store

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered
