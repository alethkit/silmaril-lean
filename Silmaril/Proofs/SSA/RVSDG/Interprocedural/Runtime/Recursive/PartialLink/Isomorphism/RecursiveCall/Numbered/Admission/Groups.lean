module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.AdmissionProofs

open Continuation.Partial (Primitives)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {members : List (Function V S)} {primitives : Primitives m σ} {ids : GlobalRel}

private abbrev HasOrdinary (family : Family m) : Prop :=
  ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → family value

private theorem ordinary_tuple {family : Family m} (admits : HasOrdinary family)
    {ports : Ports (Ty V S)} (tuple : Tuple m.Val ports) (ordinary : ordinaryPorts ports = true) :
    TupleIn family tuple := by
  induction tuple with
  | nil => trivial
  | cons value tail ih =>
    have both := Bool.and_eq_true_iff.mp ordinary
    exact ⟨admits value both.1, ih both.2⟩

private theorem closed_with_captures {family : Family m}
    (ordinary : OrdinaryOutputs Op) (admits : HasOrdinary family)
    (captures : ∀ {args outs : Ports (Ty V S)} {callee : m.Val (.value (.function args outs))},
      family callee → TupleIn family (resolve m callee).values) : Closed primitives family where
  captures := captures
  primitive := by
    intro _ _ opcode _ _ _ _ output _
    exact ordinary_tuple admits output (ordinary opcode)

private theorem member_values (family : Family m) (members : List (Function V S))
    (refs : (slot : Fin members.length) → m.Val members[slot].port)
    (known : ∀ slot, family (refs slot)) : TupleIn family (memberValues members refs) := by
  induction members with
  | nil => trivial
  | cons _ _ ih => exact ⟨known 0, ih _ (fun _ => known _)⟩

private theorem member_prefix (family : Family m) (members : List (Function V S)) (n : Nat)
    (refs : (slot : Fin members.length) → m.Val members[slot].port)
    (known : ∀ slot, family (refs slot)) : LocalsIn family (memberPrefix members n refs) := by
  induction members generalizing n with
  | nil => cases n <;> trivial
  | cons _ _ ih =>
    cases n with
    | zero => trivial
    | succ n => exact ⟨⟨known 0, trivial⟩, ih n _ (fun _ => known _)⟩

private theorem closed (ordinary : OrdinaryOutputs Op) (group : Group m members)
    (outer : ordinaryPorts group.context = true) : Closed primitives group.In := by
  apply closed_with_captures ordinary Group.In.ordinary
  intro args outs callee admitted
  cases admitted with
  | ordinary _ plain => cases plain
  | member slot =>
    have refs := member_values group.In members group.ref (fun i => .member i)
    have earlier := member_prefix group.In members slot.val group.ref (fun i => .member i)
    exact TupleIn.read (group.definitions slot).captures
      (TupleIn.prepend refs (ordinary_tuple Group.In.ordinary group.values outer)) earlier

private theorem member_origin {group : Group m members} {port : Ty V S} {value : m.Val port}
    (known : group.In value) (callable : ordinaryPort port = false) :
    ∃ slot : Fin members.length,
      (⟨port, value⟩ : (t : Ty V S) × m.Val t) = ⟨members[slot].port, group.ref slot⟩ := by
  cases known with
  | ordinary _ plain => rw [callable] at plain; cases plain
  | member slot => exact ⟨slot, rfl⟩

private def slotNumber {port : Ty V S} : m.Val port → Option Nat
  | .member _ _ slot => some slot.val
  | _ => none

private theorem related_slot {port : Ty V S} {left right : m.Val port}
    (related : ValueRelated m ids left right) : slotNumber left = slotNumber right := by
  cases related <;> rfl

private theorem closed_standalone (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    (root : m.Val (.value (.function args outs))) (plain : ordinaryPorts (resolve m root).context = true) :
    Closed primitives (StandaloneIn root) := by
  apply closed_with_captures ordinary StandaloneIn.ordinary
  intro _ _ _ known
  cases known with
  | ordinary _ plain => cases plain
  | exported => exact ordinary_tuple StandaloneIn.ordinary (resolve m root).values plain

private theorem checked_standalone (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    (left right : m.Val (.value (.function args outs)))
    (plainL : ordinaryPorts (resolve m left).context = true)
    (plainR : ordinaryPorts (resolve m right).context = true)
    (checked : Resolved m ⟨args, outs⟩ (resolve m left) (resolve m right)) :
    CheckedFamily primitives ids (StandaloneIn left) (StandaloneIn right) := by
  refine ⟨closed_standalone ordinary left plainL, closed_standalone ordinary right plainR, ?_⟩
  intro _ _ _ _ knownL knownR _
  cases knownL with
  | ordinary _ plain => cases plain
  | exported =>
    cases knownR with
    | ordinary _ plain => cases plain
    | exported => exact checked

variable [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key]

private theorem checked_groups (ordinary : OrdinaryOutputs Op) (left right : Group m members)
    (accepted : checkGroups keys left right = true) :
    CheckedFamily primitives ids left.In right.In := by
  obtain ⟨plain, scanned⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨plainL, plainR⟩ := Bool.and_eq_true_iff.mp plain
  refine ⟨closed ordinary left plainL, closed ordinary right plainR, ?_⟩
  have bodies (slot : Fin members.length) :
      (inferResolved keys (resolve m (left.ref slot)) (resolve m (right.ref slot))).isSome = true :=
    List.all_eq_true.mp scanned _ (List.mem_ofFn.mpr ⟨slot, rfl⟩)
  intro args outs calleeL calleeR knownL knownR related
  cases knownL with
  | ordinary _ plain => cases plain
  | member slotL =>
    obtain ⟨slotR, origin⟩ := member_origin knownR rfl
    have found := congrArg (fun pair : (t : Ty V S) × m.Val t => slotNumber pair.2) origin
    have same : slotL = slotR := Fin.ext (Option.some.inj ((related_slot related).trans found))
    subst slotR
    have exactRef : calleeR = right.ref slotL := eq_of_heq (Sigma.mk.inj_iff.mp origin).2
    subst calleeR
    exact inferResolved_sound (bodies slotL)

theorem checkExport_sound (ordinary : OrdinaryOutputs Op) {args outs : Ports (Ty V S)}
    {left right : m.Val (.value (.function args outs))}
    (accepted : checkExport keys left right = true) : ExportAdmission primitives ids left right := by
  unfold checkExport at accepted
  split at accepted
  · obtain ⟨plain, scanned⟩ := Bool.and_eq_true_iff.mp accepted
    obtain ⟨plainL, plainR⟩ := Bool.and_eq_true_iff.mp plain
    exact ⟨StandaloneIn left, StandaloneIn right,
      checked_standalone ordinary left right plainL plainR (inferResolved_sound scanned), .exported, .exported,
      fun tuple plain => ⟨ordinary_tuple StandaloneIn.ordinary tuple plain,
        ordinary_tuple StandaloneIn.ordinary tuple plain⟩⟩
  · split at accepted
    next l r _ _ =>
      obtain ⟨membersL, groupL, knownL⟩ := l
      obtain ⟨membersR, groupR, knownR⟩ := r
      split at accepted
      next same =>
        change membersL = membersR at same
        subst membersR
        exact ⟨groupL.In, groupR.In, checked_groups ordinary groupL groupR accepted, knownL, knownR,
          fun tuple plain => ⟨ordinary_tuple Group.In.ordinary tuple plain,
            ordinary_tuple Group.In.ordinary tuple plain⟩⟩
      next => cases accepted
    next => cases accepted

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.AdmissionProofs
