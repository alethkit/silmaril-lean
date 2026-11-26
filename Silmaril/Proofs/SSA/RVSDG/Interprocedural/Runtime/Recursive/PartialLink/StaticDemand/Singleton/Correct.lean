module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Correct
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness (Demand)
open NestedTheta.Liveness.Demand.Proofs (read_selected)
open Continuation.Partial.Executable (Actions)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {summary : MemberSummary V S} {imports : Ports (Ty V S)}
variable (family : Singleton Op summary imports)

private def asFamily : Family Op summary.singleton imports where
  context := summary.captures
  captures := family.captures
  memberWires := Fin.cases family.memberWires (fun i => i.elim0)
  sigs := fun _ => family.sigs
  body := Fin.cases family.body (fun i => i.elim0)
  closed := by
    intro i demand
    refine Fin.cases ?_ (fun j => j.elim0) i
    refine ⟨?_, ?_⟩
    · intro p inside
      change p < 1 at inside
      have h : p = 0 := by omega
      exact h ▸ (family.closed demand).1
    · intro p live
      change .arg (1 + p) ∈ (family.body.plan demand).live at live
      exact (family.closed demand).2 p (by simpa only [Nat.add_comm] using live)

private theorem capturedAt (captured : Tuple m.Val summary.captures) (ready : family.Ready captured) :
    (asFamily family).capturedAt captured (0 : Fin 1) = captured := by
  unfold Family.capturedAt
  change Family.dropPrefix [summary.fn.port]
    (family.memberWires.read (prependContext (.cons (family.memberValue captured) .nil) captured) PUnit.unit) = _
  rw [ready.1]
  rfl

private theorem familyReady (captured : Tuple m.Val summary.captures) (ready : family.Ready captured) :
    (asFamily family).Ready captured := by
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  have captures := capturedAt family captured ready
  have guards : (asFamily family).guard captured = family.guard captured := by
    funext j
    refine Fin.cases ?_ (fun k => k.elim0) j
    unfold Family.guard
    rw [captures]
    rfl
  constructor
  · rw [captures]
    exact ready.1
  · intro params
    unfold Family.entry
    rw [guards]
    change family.body.ResolvedWith (family.guard captured)
      (prependContext params
        (family.memberWires.read (prependContext (.cons (family.memberValue captured) .nil) captured) PUnit.unit))
    rw [ready.1]
    exact ready.2 params

theorem singleton_calls (actions : Actions m σ) (demand : Demand)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val summary.fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (family.invocation importedL argsL), store⟩
      ⟨Continuation.start (family.invocation importedR argsR), store⟩ := by
  apply (asFamily family).calls_prefix (0 : Fin 1) actions demand importedL importedR argsL argsR store
    (familyReady family _ readyL) (familyReady family _ readyR)
  unfold Family.AgreesOnInputs
  dsimp only
  change ∀ {ty} (p : Port (summary.captures ++ summary.fn.args) ty), .arg p.index ∈ summary.live demand →
    (prependContext argsL ((asFamily family).capturedAt (family.captures.read importedL PUnit.unit) (0 : Fin 1))).get p =
    (prependContext argsR ((asFamily family).capturedAt (family.captures.read importedR PUnit.unit) (0 : Fin 1))).get p
  rw [capturedAt family _ readyL, capturedAt family _ readyR]
  apply prepend_agrees (fun i => Address.arg i ∈ summary.live demand)
  · intro ty q needed
    apply read_selected (fun _ i => (summary.live demand).contains (.arg i)) family.captures
    · intro ty edge selected
      cases edge with
      | output i _ => exact i.elim0
      | arg p => exact agree.1 p selected
    · exact List.contains_iff_mem.2 needed
  · exact agree.2

theorem singleton_linked (actions : Actions m σ) (demand : Demand) (fuel after unitId : Nat)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val summary.fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∃ left right,
      family.run actions fuel unitId importedL argsL store = .ok left ∧
      family.run actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right := by
  have related := PrefixMatches.observes fuel after (singleton_calls family actions demand importedL importedR
    argsL argsR store readyL readyR agree _)
  exact ⟨_, _, rfl, rfl, related⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
