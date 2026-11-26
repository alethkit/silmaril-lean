module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Sources

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered (linkedLambda)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)} {scope : Scope m}
variable {fn : Function V S}
variable {inputsL inputsR : Tuple m.Val imports}

theorem widen_read {args users head : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past users) (inputs : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val head) :
    (widen wires).read inputs (locals.snoc value) = wires.read inputs locals :=
  Proofs.widen_read wires inputs locals value

theorem seed_selects (family : StaticDemand.Family Op table imports) (i : Fin table.members.length)
    (inputs : Tuple m.Val imports) (origins : Wires imports [memberPorts table.members] (table.at i).captures)
    (found : phiCaptures family i = some origins) :
    let seeded := Scope.seed family inputs inputs
    selects seeded.guardL i ((seedWires i origins).read inputs seeded.localsL) :=
  Proofs.seed_selects family i inputs origins found

theorem new_selects (binding : Binding Op scope.table imports scope.past fn)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table) :
    selects (binding.extendGuard guard inputs locals) (0 : Fin (scope.table.members.length + 1))
      ((newWires binding).read inputs (locals.snoc (.cons (binding.value inputs locals) .nil))) :=
  Proofs.new_selects binding inputs locals guard

theorem projected_call {context params : Ports (Ty V S)} (captures : Wires imports scope.past context)
    (i : Fin scope.table.members.length)
    (target : Port (context ++ params) (scope.table.at i).fn.port)
    (witnesses : Wires (context ++ params) [] (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : project captures (.cons (.arg target) witnesses) = some sources)
    (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs locals)) (args : Tuple m.Val params) :
    let entry := prependContext args (captures.read inputs locals)
    guard i (entry.get target) (witnesses.read entry PUnit.unit) :=
  Proofs.projected_call captures i target witnesses sources expected found same inputs locals guard resolved args

@[expose] def Routes.seed (family : StaticDemand.Family Op table imports) (inputsL inputsR : Tuple m.Val imports) :
    Routes inputsL inputsR (Scope.seed family inputsL inputsR) :=
  fun i =>
    match found : phiCaptures family i with
    | none => none
    | some captures =>
      some ⟨seedWires i captures,
        seed_selects family i inputsL captures found, seed_selects family i inputsR captures found⟩

@[expose] def Routes.add (routes : Routes inputsL inputsR scope)
    (binding : Binding Op scope.table imports scope.past fn) :
    Routes inputsL inputsR (scope.add binding inputsL inputsR) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact some ⟨newWires binding,
      new_selects binding inputsL scope.localsL scope.guardL, new_selects binding inputsR scope.localsR scope.guardR⟩
  · exact (routes j).map fun route =>
      ⟨widen route.wires,
        (widen_read route.wires inputsL scope.localsL (.cons (binding.value inputsL scope.localsL) .nil)).symm ▸ route.left,
        (widen_read route.wires inputsR scope.localsR (.cons (binding.value inputsR scope.localsR) .nil)).symm ▸ route.right⟩

@[expose] def Routes.skip (routes : Routes inputsL inputsR scope)
    (definition : LambdaTerm Op imports scope.past fn) :
    Routes inputsL inputsR (scope.skip definition inputsL inputsR) := fun i =>
  (routes i).map fun route =>
    ⟨widen route.wires,
      (widen_read route.wires inputsL scope.localsL
        (.cons (linkedLambda definition.toGraph inputsL scope.localsL) .nil)).symm ▸ route.left,
      (widen_read route.wires inputsR scope.localsR
        (.cons (linkedLambda definition.toGraph inputsR scope.localsR) .nil)).symm ▸ route.right⟩

section Check

variable {context : Ports (Ty V S)} {actions : Actions m σ}

@[expose] def resolved {past sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (captures : Wires imports scope.past context)
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table))
    (inputsL inputsR : Tuple m.Val imports) : Prop :=
  (∀ args, code.ResolvedWith scope.guardL (prependContext args (captures.read inputsL scope.localsL))) ∧
  (∀ args, code.ResolvedWith scope.guardR (prependContext args (captures.read inputsR scope.localsR)))

/-- Certify a straight-line body by comparing the target and witness wires
at their exact typed linker addresses. Each callable origin must also
have checked membership on both sides. Local outputs, formal callees,
inline closure descriptions, and region forwarding require explicit
resolution instead. -/
@[expose] def synthesizeSteps (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope)
    (captures : Wires imports scope.past context) :
    Nat → {past sigs : List (Ports (Ty V S))} → {outs : Ports (Ty V S)} →
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table)) →
    Option (PLift (resolved captures code inputsL inputsR))
  | _, _, _, _, .ret _ => some ⟨fun _ => trivial, fun _ => trivial⟩
  | steps + 1, _, _, _, .primitive _ _ rest => synthesizeSteps checked routes captures steps rest
  | steps + 1, _, _, _, .familyCall i target witnesses _ rest =>
    match found : project captures (.cons (.arg target) witnesses), routes i with
    | some sources, some route =>
      if same : sources.addresses = route.wires.addresses then
        let origin := sources.get .head
        if (checked.state.left.available (entry := inputsL) Known.ordinary origin).isSome &&
            (checked.state.right.available (entry := inputsR) Known.ordinary origin).isSome then
          (synthesizeSteps checked routes captures steps rest).map fun later =>
            ⟨fun args => ⟨projected_call captures i target witnesses sources route.wires found same
                inputsL scope.localsL scope.guardL route.left args, later.down.1 args⟩,
              fun args => ⟨projected_call captures i target witnesses sources route.wires found same
                inputsR scope.localsR scope.guardR route.right args, later.down.2 args⟩⟩
        else none
      else none
    | _, _ => none
  | _, _, _, _, _ => none
termination_by structural steps _ _ _ _ => steps

@[expose] def synthesize (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope)
    (captures : Wires imports scope.past context) {past sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table)) :
    Option (PLift (resolved captures code inputsL inputsR)) :=
  synthesizeSteps checked routes captures sigs.length code

end Check

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct
