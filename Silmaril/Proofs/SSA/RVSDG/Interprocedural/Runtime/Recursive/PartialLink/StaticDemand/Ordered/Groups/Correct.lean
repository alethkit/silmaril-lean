module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Proofs

open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {actions : Actions m σ} {earlier later : MemberSummaries V S}
variable {imports exports : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

private theorem transport {source target : MemberSummary V S} (same : source = target)
    (left right : SlotGuard m source) (sound : DispatchAt actions source left right) :
    DispatchAt actions target (same ▸ left) (same ▸ right) := by
  subst target
  exact sound

theorem combine (old : Dispatch actions earlier) (new : Dispatch actions later) :
    ∀ i, DispatchAt actions ((append earlier later).at i) ((old.left.combine new.left) i)
      ((old.right.combine new.right) i) :=
  slotCases earlier later
    (result := fun i => DispatchAt actions ((append earlier later).at i)
      ((old.left.combine new.left) i) ((old.right.combine new.right) i))
    (fun j => by
      rw [Guard.combine_left, Guard.combine_left]
      exact transport (append_at_old earlier later j).symm _ _ (old.transport j))
    (fun j => by
      rw [Guard.combine_right, Guard.combine_right]
      exact transport (append_at_new earlier later j).symm _ _ (new.transport j))

private theorem atSlot {table : MemberSummaries V S} {guard : Guard m table}
    (i : Fin table.members.length) {source : MemberSummary V S}
    (same : source = table.at i) (test : SlotGuard m source)
    (reads : guard i = (same ▸ test)) (f : m.Val source.fn.port)
    (caps : Tuple m.Val source.captures) (known : test f caps) : Known guard f := by
  subst source
  exact .callable i f caps (reads.symm ▸ known)

theorem oldKnown {left : Guard m earlier} (right : Guard m later)
    {ty : Ty V S} {value : m.Val ty} : Known left value → Known (left.combine right) value
  | .ordinary value plain => .ordinary value plain
  | .callable i f caps known =>
    atSlot (leftIndex earlier later i) (append_at_old earlier later i).symm (left i)
      (Guard.combine_left left right i) f caps known

theorem newKnown (left : Guard m earlier) {right : Guard m later}
    {ty : Ty V S} {value : m.Val ty} : Known right value → Known (left.combine right) value
  | .ordinary value plain => .ordinary value plain
  | .callable i f caps known =>
    atSlot (rightIndex earlier later i) (append_at_new earlier later i).symm (right i)
      (Guard.combine_right left right i) f caps known

theorem link_step (binding : GroupBinding Op later imports past)
    (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val imports)
    (locals : Locals m.Val past) (rest : ModuleTerm Op imports (past ++ [memberPorts later.members]) sigs exports)
    (store : σ) :
    Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs locals (.bind (.phi binding.term) rest) store =
      Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm actions unitId inputs (binding.locals inputs locals) rest store := by
  rw [Isomorphism.RecursiveCall.Numbered.Prefix.linkTerm_bind]
  rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.Proofs
