module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Singleton.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Correct
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs

open NestedTheta.Liveness (Demand)
open NestedTheta.Liveness.Demand.Proofs (ScopeAgrees read_selected)
open Continuation (Stack)
open Continuation.Partial (Config)
open Continuation.Partial.Executable (Actions next? observe runFor)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {summary : MemberSummary V S} {imports final : Ports (Ty V S)}
variable (family : Singleton Op summary imports)

private theorem opens (captured : Tuple m.Val summary.captures) (args : Tuple m.Val summary.fn.args)
    (ready : family.Ready captured) :
    Job.openClosure m (family.memberValue captured) args =
      .region family.body.term (family.entry captured args) PUnit.unit := by
  change Job.region family.body.term.toGraph.toTerm
    (prependContext args (family.memberWires.read
      (prependContext (.cons (family.memberValue captured) .nil) captured) PUnit.unit))
    (PUnit.unit : Locals m.Val []) = _
  rw [ready.1, NestedTheta.Term.toTerm_toGraph]
  rfl

private theorem body_agrees (wanted : Demand)
    {capturedL capturedR : Tuple m.Val summary.captures} {argsL argsR : Tuple m.Val summary.fn.args}
    (live : ScopeAgrees (scope := []) (summary.live wanted)
      (prependContext argsL capturedL) (prependContext argsR capturedR) PUnit.unit PUnit.unit) :
    ScopeAgrees (scope := []) (family.body.plan wanted).live
      (family.entry capturedL argsL) (family.entry capturedR argsR) PUnit.unit PUnit.unit := by
  intro ty source needed
  cases source with
  | output i _ => exact i.elim0
  | arg p =>
    cases p with
    | head => exact False.elim ((family.closed wanted).1 needed)
    | tail p => exact live (.arg p) ((family.closed wanted).2 p.index needed)

/-- Use one actual dispatch step before reusing the certified family. The
induction ranges over observation depth and is independent of call depth. -/
private theorem member_prefix (actions : Actions m σ) (observed : Demand)
    (capturedL capturedR : Tuple m.Val summary.captures)
    (readyL : family.Ready capturedL) (readyR : family.Ready capturedR) (budget : Nat) :
    ∀ (wanted : Demand) (argsL argsR : Tuple m.Val summary.fn.args)
      (store : σ) (left right : Stack m summary.fn.results final),
      ScopeAgrees (scope := []) (summary.live wanted)
        (prependContext argsL capturedL) (prependContext argsR capturedR) PUnit.unit PUnit.unit →
      ResumeAgrees actions observed wanted (some budget) left right (fun _ => True) (fun _ => True) →
      PrefixMatches actions observed budget
        ⟨.eval (.call (family.memberValue capturedL) argsL) left, store⟩
        ⟨.eval (.call (family.memberValue capturedR) argsR) right, store⟩ := by
  induction budget using Nat.strong_induction_on with
  | ind budget ih =>
    intro wanted argsL argsR store left right live finish
    cases budget with
    | zero => exact .cut _ _
    | succ n =>
      have enter (captured : Tuple m.Val summary.captures) (args : Tuple m.Val summary.fn.args)
          (frame : Stack m summary.fn.results final) (ready : family.Ready captured) :
          next? actions ⟨.eval (.call (family.memberValue captured) args) frame, store⟩ =
            some ⟨.eval (.region family.body.term (family.entry captured args) PUnit.unit) frame, store⟩ := by
        change some (⟨.eval (Job.openClosure m (family.memberValue captured) args) frame, store⟩ :
          Config m σ final) = _
        rw [opens family captured args ready]
      have dispatch : MemberDispatch actions observed (family.guard capturedL) (family.guard capturedR) n final := by
        intro depth bounded requested fL fR capL capR argL argR middle frameL frameR hL hR agree resume
        obtain ⟨rfl, rfl⟩ := hL
        obtain ⟨rfl, rfl⟩ := hR
        exact ih depth (Nat.lt_succ_of_le bounded) requested argL argR middle frameL frameR agree resume
      apply PrefixMatches.step (enter capturedL argsL left readyL) (enter capturedR argsR right readyR)
      apply region actions observed family.body (family.guard capturedL) (family.guard capturedR)
        (some n) (by simp) dispatch wanted _ _ PUnit.unit PUnit.unit left right store
        (readyL.2 argsL) (readyR.2 argsR) (body_agrees family wanted live)
      intro outL outR middle agree _ _
      exact prefix_mono (Nat.le_succ n) (finish outL outR middle agree trivial trivial)

theorem singleton_calls (actions : Actions m σ) (demand : Demand)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val summary.fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∀ depth, PrefixMatches actions demand depth
      ⟨Continuation.start (family.invocation importedL argsL), store⟩
      ⟨Continuation.start (family.invocation importedR argsR), store⟩ := by
  intro depth
  apply member_prefix family actions demand _ _ readyL readyR depth demand argsL argsR store .halt .halt
  · intro ty source live
    cases source with
    | output i _ => exact i.elim0
    | arg p =>
      apply prepend_agrees (fun i => Address.arg i ∈ summary.live demand)
      · intro ty q needed
        apply read_selected (fun _ i => (summary.live demand).contains (.arg i)) family.captures
        · intro ty edge selected
          cases edge with
          | output i _ => exact i.elim0
          | arg p => exact agree.1 p selected
        · exact List.contains_iff_mem.2 needed
      · exact agree.2
      · exact live
  · intro outL outR middle demanded _ _
    cases depth with
    | zero => exact PrefixMatches.cut _ _
    | succ n => exact PrefixMatches.returned demanded

theorem singleton_linked (actions : Actions m σ) (demand : Demand) (fuel after unitId : Nat)
    (importedL importedR : Tuple m.Val imports) (argsL argsR : Tuple m.Val summary.fn.args) (store : σ)
    (readyL : family.Ready (family.captures.read importedL PUnit.unit))
    (readyR : family.Ready (family.captures.read importedR PUnit.unit))
    (agree : family.AgreesOnInputs demand importedL importedR argsL argsR) :
    ∃ left right,
      family.run actions fuel unitId importedL argsL store = .ok left ∧
      family.run actions fuel unitId importedR argsR store = .ok right ∧
      PrefixObservationsAgree actions demand after left right := by
  have related := prefix_observes fuel after (singleton_calls family actions demand importedL importedR
    argsL argsR store readyL readyR agree _)
  exact ⟨_, _, rfl, rfl, related⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Proofs
