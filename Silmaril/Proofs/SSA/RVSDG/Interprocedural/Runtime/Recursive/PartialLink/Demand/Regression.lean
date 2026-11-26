module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Regression

open NestedTheta.Liveness (Demand)
open Continuation.Partial (Site)
open Continuation.Partial.Executable (Actions Observation observe runFor)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev pair := [num, num]
private abbrev triple := [num, num, num]
private abbrev caller : Function Unit Unit := ⟨triple, triple⟩
private abbrev callee : Function Unit Unit := ⟨pair, pair⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | probe : Op pair [num]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .probe, .cons (.data captured) (.cons (.data input) .nil) =>
      .cons (.data (captured + input)) .nil

private def numbers (a b : Nat) : Tuple machine.Val pair := .cons (.data a) (.cons (.data b) .nil)

private def values (a b c : Nat) : Tuple machine.Val triple :=
  .cons (.data a) (.cons (.data b) (.cons (.data c) .nil))

private def actions : Actions machine Nat where
  step
    | .probe, .cons (.data captured) (.cons (.data input) .nil) => fun store =>
      let captured : Nat := captured
      let input : Nat := input
      if captured = 7 ∧ input = 0 then none
      else some (.cons (.data (captured + input + store)) .nil, store + 2)

private def call : DirectCall Op pair caller callee where
  context := pair
  captures := .cons (.arg (.tail .head)) (.cons (.arg .head) .nil)
  ins := pair
  outs := [num]
  opcode := .probe
  operands := .cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil)
  calleeResults := .cons (.output 0 .head) (.cons (.arg (.tail .head)) .nil)
  arguments := .cons (.arg (.tail .head)) (.cons (.arg .head) .nil)
  callerResults := .cons (.output 0 (.tail .head)) (.cons (.arg (.tail (.tail .head)))
    (.cons (.output 0 .head) .nil))

private def requested : Demand := fun p => p == 1 || p == 2

-- Numbering differs across the capture, argument and result boundaries.
-- The shared summary drops the forwarded capture only at this demand.
example : call.calleeLiveIn requested = [.arg 0, .arg 2] := by decide
example : call.liveImports requested = [.arg 1] := by decide
example : call.liveArguments requested = [.arg 2, .arg 1] := by decide
example : call.liveImports (fun _ => true) = [.arg 1, .arg 0] := by decide
example : call.liveImports (fun _ => false) = [.arg 1] := by decide
example : call.liveArguments (fun _ => false) = [.arg 1] := by decide
example : Address.arg 2 ∈ (call.calleeLiveness requested).mayOut 0 :=
  (call.mem_calleeLiveIn_iff requested _).1 (by decide)

private theorem input_agreement (operand : Nat) :
    call.AgreesOnInputs requested (numbers 9 7) (numbers 90 7)
      (values 4 operand 11) (values 40 operand 11) := by
  constructor
  · intro ty p live
    cases p with
    | head => exact False.elim ((by decide : Address.arg 0 ∉ call.liveImports requested) live)
    | tail p =>
      cases p with
      | head => rfl
      | tail p => nomatch p
  · intro ty p live
    cases p with
    | head => exact False.elim ((by decide : Address.arg 0 ∉ call.liveArguments requested) live)
    | tail p =>
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => rfl
        | tail p => nomatch p

-- Both linked closures execute the primitive with capture 7, argument 3
-- and initial store 20. The undemanded first output can differ.
example : call.run actions 10 73 (numbers 9 7) (values 4 3 11) 20 =
    .ok (.returned (values 9 11 30) 22) := rfl
example : call.run actions 10 73 (numbers 90 7) (values 40 3 11) 20 =
    .ok (.returned (values 90 11 30) 22) := rfl

-- At the would-be blocking argument, changing the live capture to 8
-- makes the primitive return and advance the store.
example : call.run actions 10 73 (numbers 9 8) (values 4 0 11) 20 =
    .ok (.returned (values 9 11 28) 22) := rfl

-- The linked runner exposes a real suspended machine configuration at
-- budget five. Resuming it runs the primitive and both saved suffixes.
example : (call.run actions 5 73 (numbers 90 7) (values 40 3 11) 20).map
    (fun outcome => match outcome with
      | .suspended config => some (observe actions (runFor actions 5 config))
      | _ => none) = .ok (some (.returned (values 90 11 30) 22)) := rfl

private def blockedSite : Site machine :=
  ⟨pair, [num], .probe, fun i => i.elim0, fun i => i.elim0, numbers 7 0⟩

private theorem probeSite_eq (site : Site machine) :
    (match site with
     | ⟨_, _, .probe, _, _, input⟩ => input = numbers 7 0) → site = blockedSite := by
  obtain ⟨ins, outs, opcode, cs, children, input⟩ := site
  cases opcode
  intro same
  change input = numbers 7 0 at same
  subst input
  have cs_eq : cs = fun i => i.elim0 := funext fun i => i.elim0
  subst cs
  have children_eq : children = fun i => i.elim0 := funext fun i => i.elim0
  subst children
  rfl

private def exactBlock (outcome : Except (Failure machine Nat) (Observation machine Nat triple)) : Prop :=
  match outcome with
  | .ok (.blocked active store) =>
    active.site = blockedSite ∧ store = 20 ∧ Continuation.Descent.stackDepth active.stack = 2
  | _ => False

private theorem blockedLeft : exactBlock (call.run actions 10 73 (numbers 9 7) (values 4 0 11) 20) :=
  ⟨probeSite_eq _ rfl, rfl, rfl⟩

example : exactBlock (call.run actions 10 73 (numbers 90 7) (values 40 0 11) 20) :=
  ⟨probeSite_eq _ rfl, rfl, rfl⟩

private def relatedBlock (left right : Except (Failure machine Nat) (Observation machine Nat triple)) : Prop :=
  match left, right with
  | .ok (.blocked activeL storeL), .ok (.blocked activeR storeR) =>
    ObservationsAgree actions requested (.blocked activeL storeL) (.blocked activeR storeR)
  | _, _ => False

-- The theorem relates the actual saved stacks through continuation behavior.
example : relatedBlock (call.run actions 10 73 (numbers 9 7) (values 4 0 11) 20)
    (call.run actions 10 73 (numbers 90 7) (values 40 0 11) 20) := by
  obtain ⟨left, right, ranL, ranR, related⟩ :=
    call.run_agrees actions 73 0 requested (numbers 9 7) (numbers 90 7)
      (values 4 0 11) (values 40 0 11) 20 (input_agreement 0)
  have blocked := blockedLeft
  rw [ranL] at blocked
  rw [ranL, ranR]
  cases related with
  | returned => exact False.elim blocked
  | blocked saved => exact .blocked saved

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Demand.Regression
