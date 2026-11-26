module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Defs

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Regression

open NestedTheta.Liveness
open Continuation (Stack)
open Continuation.Partial (Config Step)
open Continuation.Partial.Executable (Actions Observation next? observe runFor runFor_add step_iff)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev pair := [num, num]
private abbrev fn : Function Unit Unit := ⟨[num, num, num], pair⟩
private abbrev entry := [fn.port, fn.port, num, num, num, num]
private abbrev decision : List T := [.control 2, num]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | route (first : Bool) : Op single decision
  | probe : Op single []
  | after : Op [] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .route _, .cons (.data count) .nil => .cons (.control 0) (.cons (.data count) .nil)
    | .probe, _ => .nil
    | .after, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil
private def two (a b : Nat) : Tuple machine.Val pair := .cons (.data a) (one b)

private def actions : Actions machine Nat where
  step
    | .route first, .cons (.data count) .nil => fun store =>
      let count : Nat := count
      let tag : Fin 2 := if count = 0 then 0 else 1
      let next := if count = 99 then count else count - 1
      some (.cons (.control tag) (one next), store + (if first then 1 else 2))
    | .probe, .cons (.data cap) .nil => fun store =>
      let cap : Nat := cap
      if cap = 0 then none else some (.nil, store + cap)
    | .after, _ => fun store => some (.nil, store + 10)

private def required (first : Bool) (demand : Demand) : List Address :=
  [.arg 0, .arg 1] ++ (if demand 0 then [.arg (if first then 2 else 3)] else []) ++
    (if demand 1 then [.arg (if first then 3 else 2)] else [])

private abbrev summaries : MemberSummaries Unit Unit where
  members := [fn, fn]
  captures := fun _ => single
  live := Fin.cases (required true) (fun _ => required false)
  monotone := by
    intro i low high le
    refine Fin.cases ?_ (fun _ => ?_) i <;>
      change required _ low ⊆ required _ high <;> clear i
    all_goals
      have selected (p : Nat) (a : Address) :
          (if low p then [a] else []) ⊆ (if high p then [a] else []) := by
        intro b h
        by_cases active : low p = true
        · simpa only [ite_eq_left active, ite_eq_left (le p active)] using h
        · simp [active] at h
      intro a h
      simp only [required, List.mem_append] at h ⊢
      exact h.imp (fun h => h.imp id (fun h => selected 0 _ h)) (fun h => selected 1 _ h)

private def capture : Port entry num := .tail (.tail .head)
private def count : Port entry num := .tail (.tail (.tail .head))
private def payload : Port entry num := .tail (.tail (.tail (.tail .head)))
private def spare : Port entry num := .tail (.tail (.tail (.tail (.tail .head))))

private def baseArm (first : Bool) : Code Op entry [] [[]] pair true (some summaries) :=
  .primitive .probe (.cons (.arg capture) .nil)
    (.ret (if first then .cons (.arg payload) (.cons (.arg spare) .nil)
      else .cons (.arg spare) (.cons (.arg payload) .nil)))

-- The two members expose payload at different result ports.
private def afterCall : Code Op entry [pair] [[]] pair true (some summaries) :=
  .primitive .after .nil
    (.ret (.cons (.output (0 : Fin 2) (.tail .head)) (.cons (.output (0 : Fin 2) .head) .nil)))

private def recursiveArm (first : Bool) : Code Op entry [] [pair, []] pair true (some summaries) :=
  let captured : Wires entry [] single := .cons (.arg capture) .nil
  let args : Wires entry [] fn.args := .cons (.arg count) (.cons (.arg payload) (.cons (.arg spare) .nil))
  if first then .familyCall (table := summaries) 1 (.tail .head) captured args afterCall
  else .familyCall (table := summaries) 0 .head captured args afterCall

private def armSigs : Fin 2 → List (Ports T) := Fin.cases [[]] (fun _ => [pair, []])

private def arms (first : Bool) (i : Fin 2) : Code Op entry [] (armSigs i) pair true (some summaries) :=
  Fin.cases (motive := fun j => Code Op entry [] (armSigs j) pair true (some summaries))
    (baseArm first) (fun _ => recursiveArm first) i

private def body (first : Bool) : Code Op entry [] [decision, pair] pair true (some summaries) :=
  let captures : Wires entry [decision] entry :=
    .cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons (.arg capture) (.cons (.output (0 : Fin 1) (.tail .head))
        (.cons (.arg payload) (.cons (.arg spare) .nil)))))
  .primitive (.route first) (.cons (.arg count) .nil)
    (.gamma 0 armSigs (.output (0 : Fin 1) .head) captures (arms first)
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))

private theorem body_live (first : Bool) (d : Demand) :
    ((body first).plan d).live =
      [.arg 3, .arg 2] ++ (if (if first then d 0 else d 1) then [.arg 4] else []) ++
        (if (if first then d 1 else d 0) then [.arg 5] else []) := by
  cases first <;> cases h0 : d 0 <;> cases h1 : d 1 <;>
    simp (config := { decide := true }) [body, arms, armSigs, baseArm, recursiveArm, afterCall, capture, count, payload,
      spare, summaries, Code.plan, DemandPlan.prepend, transfer, selectWires,
      Demand.observes, NestedTheta.Kind.demandReads, Wires.addresses, Origin.address, Port.index, definedAt,
      h0, h1]

private theorem closedBody (first : Bool) (d : Demand) :
    (∀ p, p < 2 → .arg p ∉ ((body first).plan d).live) ∧
    ∀ p, .arg (2 + p) ∈ ((body first).plan d).live → .arg p ∈ required first d := by
  rw [body_live first d]
  cases first <;> cases h0 : d 0 <;> cases h1 : d 1 <;>
    simp [required, h0, h1, List.mem_cons] <;>
      exact ⟨by intro p hp; omega, by intro p hp; omega⟩

private def family : Family Op summaries single where
  context := single
  captures := .cons (.arg .head) .nil
  memberWires := Fin.cases
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) (.cons (.arg .head) .nil)))
    (Fin.cases (.cons (.output (0 : Fin 1) .head)
      (.cons (.arg (.tail (.tail .head))) (.cons (.arg .head) .nil))) (fun j => j.elim0))
  sigs := fun _ => [decision, pair]
  body := Fin.cases (body true) (Fin.cases (body false) (fun j => j.elim0))
  closed := by
    intro i d
    refine Fin.cases (closedBody true d) (fun j => ?_) i
    obtain rfl := Fin.eq_zero j
    exact closedBody false d

private def requested : Demand := fun p => p == 0
private def requestedSecond : Demand := fun p => p == 1
private def empty : Demand := fun _ => false

-- Both edges require payload only through the demanded callee result.
example : (recursiveArm true).liveIn requested = [.arg 2, .arg 3, .arg 4] := by decide
example : (recursiveArm false).liveIn requestedSecond = [.arg 2, .arg 3, .arg 4] := by decide
example : (recursiveArm true).liveIn empty = [.arg 2, .arg 3] := by decide
example : (recursiveArm false).liveIn empty = [.arg 2, .arg 3] := by decide
example : Address.arg 4 ∈ ((body true).liveness requested).mayOut 0 :=
  (Code.mem_liveIn_iff (body true) requested _).1 (by decide)

private def args (count payload spare : Nat) : Tuple machine.Val fn.args :=
  .cons (.data count) (two payload spare)

private theorem ready (cap : Nat) : family.Ready (m := machine) (one cap) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨rfl, fun params => ⟨?_, trivial⟩⟩
    intro locals arm
    refine Fin.cases ?_ (fun _ => ?_) arm
    · trivial
    · exact ⟨⟨rfl, rfl⟩, trivial⟩
  · obtain rfl := Fin.eq_zero j
    refine ⟨rfl, fun params => ⟨?_, trivial⟩⟩
    intro locals arm
    refine Fin.cases ?_ (fun _ => ?_) arm
    · trivial
    · exact ⟨⟨rfl, rfl⟩, trivial⟩

private theorem agreed (cap n : Nat) :
    family.AgreesOnInputs 0 requested (one cap) (one cap) (args n 41 4) (args n 41 40) := by
  intro ty p live
  cases p with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p =>
      cases p with
      | head => rfl
      | tail p =>
        cases p with
        | head => exact False.elim ((by decide : Address.arg 3 ∉ required true requested) live)
        | tail p => nomatch p

private def run (fuel cap count spare : Nat) :=
  family.run 0 actions fuel 83 (one cap) (args count 41 spare) 20

example (fuel after cap count : Nat) :
    ∃ left right, run fuel cap count 4 = .ok left ∧ run fuel cap count 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right :=
  family.linked_prefixes_agree 0 actions requested fuel after 83 (one cap) (one cap)
    (args count 41 4) (args count 41 40) 20 (ready cap) (ready cap) (agreed cap count)

private def returnedValues : Observation machine Nat pair → Option (Nat × Nat × Nat)
  | .returned (.cons (.data value) (.cons (.data spare) .nil)) store => some (value, spare, store)
  | _ => none

-- The recursive frame performs its post-call effect on return.
#guard (run 64 2 2 4).toOption.bind returnedValues == some (41, 4, 46)
#guard (run 64 2 2 40).toOption.bind returnedValues == some (41, 40, 46)

private def probeBlock (result : Except (Failure machine Nat) (Observation machine Nat pair)) : Bool :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data cap) .nil⟩, frames⟩ store) =>
    let input : Nat := cap
    input == 0 && store == 24 && Continuation.Descent.stackDepth frames == 6
  | _ => false

#guard probeBlock (run 64 0 2 4)
#guard probeBlock (run 64 0 2 40)

private def resume (result : Except (Failure machine Nat) (Observation machine Nat pair)) :
    Option (Observation machine Nat pair) :=
  match result with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, frames⟩ _) =>
    some (observe actions (runFor actions 40 ⟨.returned .nil frames, 50⟩))
  | _ => none

#guard (resume (run 64 0 2 4)).bind returnedValues == some (41, 4, 70)
#guard (resume (run 64 0 2 40)).bind returnedValues == some (41, 40, 70)

private def repeated (spare store : Nat) (frame : Stack machine pair pair) : Config machine Nat pair :=
  ⟨.eval (family.invocation 0 (one 2) (args 99 41 spare)) frame, store⟩

example (spare : Nat) :
    Executable.start actions 83 (family.graph 0) (one 2) .head (args 99 41 spare) 20 =
      .ok (repeated spare 20 .halt) := rfl

-- Two actual call edges add frames and return to the first member.
private def repeatedSecond (spare store : Nat) (frame : Stack machine pair pair) : Config machine Nat pair :=
  ⟨.eval (family.invocation 1 (one 2) (args 99 41 spare)) frame, store⟩

set_option maxHeartbeats 600000 in
private theorem descend (spare store : Nat) (frame : Stack machine pair pair) :
    ∃ deeper, runFor actions 16 (repeated spare store frame) = repeated spare (store + 3) deeper := by
  have first : ∃ next, runFor actions 8 (repeated spare store frame) = repeatedSecond spare (store + 1) next :=
    ⟨_, rfl⟩
  have second (next : Stack machine pair pair) :
      ∃ deeper, runFor actions 8 (repeatedSecond spare (store + 1) next) = repeated spare (store + 3) deeper :=
    ⟨_, rfl⟩
  obtain ⟨next, entered⟩ := first
  rw [show 16 = 8 + 8 by rfl, runFor_add, entered]
  exact second next

private theorem keepsStepping (spare fuel : Nat) : ∀ (store : Nat) (frame : Stack machine pair pair),
    ∃ next, next? actions (runFor actions fuel (repeated spare store frame)) = some next := by
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro store frame
    obtain ⟨deeper, reached⟩ := descend spare store frame
    by_cases enough : 16 ≤ fuel
    · rw [show fuel = 16 + (fuel - 16) by omega, runFor_add, reached]
      exact ih (fuel - 16) (by omega) (store + 3) deeper
    · cases stopped : next? actions (runFor actions fuel (repeated spare store frame)) with
      | some next => exact ⟨next, rfl⟩
      | none =>
        have fixed : runFor actions (16 - fuel) (runFor actions fuel (repeated spare store frame)) =
            runFor actions fuel (repeated spare store frame) := by
          cases 16 - fuel with
          | zero => rfl
          | succ n => simp only [runFor, stopped]
        rw [show 16 = fuel + (16 - fuel) by omega, runFor_add, fixed] at reached
        rw [reached] at stopped
        cases stopped

example (spare : Nat) : InfiniteTrace (Step actions.toPrimitives) (repeated spare 20 .halt) := by
  apply Continuation.Partial.Executable.infinite_iff_all_suspended.2
  intro fuel
  obtain ⟨next, step⟩ := keepsStepping spare fuel 20 .halt
  exact Continuation.Partial.Executable.observe_suspended.2 ⟨next, step_iff.2 step⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Regression
