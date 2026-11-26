module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.EarlierRegression

open NestedTheta.Liveness
open Continuation.Partial.Executable (Actions Observation observe runFor)
open Ordered.Prefix (Plan Scope lastExport seededGraph)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev single := [num]
private abbrev decision : List T := [.control 2, num]
private abbrev earlyFn : Function Unit Unit := ⟨single, single⟩
private abbrev lateFn : Function Unit Unit := ⟨[num, num, num], single⟩

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | decrement : Op single decision
  | probe : Op single []
  | finish : Op [] []

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .decrement, .cons (.data n) .nil => .cons (.control 0) (.cons (.data n) .nil)
    | .probe, _ => .nil
    | .finish, _ => .nil

private def one (n : Nat) : Tuple machine.Val single := .cons (.data n) .nil

private def actions : Actions machine Nat where
  step
    | .decrement, .cons (.data n) .nil => fun store =>
      let n : Nat := n
      let flag : Fin 2 := if n = 0 then 0 else 1
      some (.cons (.control flag) (one (n - 1)), store + 1)
    | .probe, .cons (.data n) .nil => fun store =>
      let n : Nat := n
      if n = 0 then none else some (.nil, store + n)
    | .finish, _ => fun store => some (.nil, store + 10)

private def demandedRead (demand : Demand) (index : Nat) : List Address :=
  if demand 0 then [.arg index] else []

private theorem input_mono (base : List Address) (index : Nat) {low high : Demand}
    (le : ∀ p, low p = true → high p = true) :
    base ++ demandedRead low index ⊆ base ++ demandedRead high index := by
  intro origin live
  cases h : low 0 with
  | false =>
    exact List.mem_append_left _ (by simpa [demandedRead, h] using live)
  | true => simpa [demandedRead, h, le 0 h] using live

private abbrev earlier : MemberSummaries Unit Unit :=
  ⟨[earlyFn], fun _ => single, fun _ d => [.arg 0] ++ demandedRead d 1, fun _ => input_mono _ _⟩

private abbrev later : MemberSummaries Unit Unit :=
  ⟨[lateFn], fun _ => [earlyFn.port, num], fun _ d => [.arg 1, .arg 2] ++ demandedRead d 3,
    fun _ => input_mono _ _⟩

private abbrev slots := Ordered.append earlier later
private abbrev earlySlot := leftIndex earlier later (0 : Fin 1)
private abbrev lateSlot := rightIndex earlier later (0 : Fin 1)
private abbrev earlyPorts := memberPorts earlier.members
private abbrev latePorts := memberPorts later.members

private def earlyBody : Code Op [earlyFn.port, num, num] [] [[]] single true (some earlier) :=
  .primitive .probe (.cons (.arg (.tail .head)) .nil)
    (.ret (.cons (.arg (.tail (.tail .head))) .nil))

private def early : Family Op earlier single where
  context := single
  captures := .cons (.arg .head) .nil
  memberWires i := Fin.cases (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil)) (fun j => j.elim0) i
  sigs := fun _ => [[]]
  body i := Fin.cases earlyBody (fun j => j.elim0) i
  closed := by
    intro i d
    obtain rfl := Fin.eq_zero i
    change (∀ p, p < 1 → Address.arg p ∉ (earlyBody.plan d).live) ∧
      ∀ p, Address.arg (1 + p) ∈ (earlyBody.plan d).live → Address.arg p ∈ earlier.live 0 d
    cases h : d 0 <;>
      simp [earlyBody, Code.plan, DemandPlan.prepend, transfer, selectWires, Wires.addresses, Origin.address,
        Demand.observes, Port.index, definedAt, demandedRead, h]; omega

private theorem earlyReady (cap : Nat) : early.Ready (one cap) := by
  intro i
  obtain rfl := Fin.eq_zero i
  exact ⟨rfl, fun _ _ _ => trivial⟩

private abbrev lateEntry := [lateFn.port, earlyFn.port, num, num, num, num]
private def capturedTarget : Port lateEntry earlyFn.port := .tail .head
private def capture : Port lateEntry num := .tail (.tail .head)
private def counter : Port lateEntry num := .tail (.tail (.tail .head))
private def payload : Port lateEntry num := .tail (.tail (.tail (.tail .head)))
private def spare : Port lateEntry num := .tail (.tail (.tail (.tail (.tail .head))))

private def base : Code Op lateEntry [] [single] single true (some slots) :=
  .familyCall (table := slots) earlySlot capturedTarget (.cons (.arg capture) .nil)
    (.cons (.arg payload) .nil) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def recurse : Code Op lateEntry [] [single, []] single true (some slots) :=
  .familyCall (table := slots) lateSlot .head (.cons (.arg capturedTarget) (.cons (.arg capture) .nil))
    (.cons (.arg counter) (.cons (.arg payload) (.cons (.arg spare) .nil)))
    (.primitive .finish .nil (.ret (.cons (.output (0 : Fin 2) .head) .nil)))

private def armSigs (i : Fin 2) : List (Ports T) := Fin.cases [single] (fun _ => [single, []]) i

private def arms (i : Fin 2) : Code Op lateEntry [] (armSigs i) single true (some slots) :=
  Fin.cases (motive := fun j => Code Op lateEntry [] (armSigs j) single true (some slots))
    base (fun _ => recurse) i

private def lateBody : Code Op lateEntry [] [decision, single] single true (some slots) :=
  let wires : Wires lateEntry [decision] lateEntry :=
    .cons (.arg .head) (.cons (.arg capturedTarget) (.cons (.arg capture)
      (.cons (.output (0 : Fin 1) (.tail .head)) (.cons (.arg payload) (.cons (.arg spare) .nil)))))
  .primitive .decrement (.cons (.arg counter) .nil)
    (.gamma 0 armSigs (.output (0 : Fin 1) .head) wires arms
      (.ret (.cons (.output (1 : Fin 2) .head) .nil)))

private theorem lateReads (d : Demand) :
    (lateBody.plan d).live = [.arg 3, .arg 2] ++ demandedRead d 4 := by
  cases h : d 0 <;>
    simp (config := { decide := true }) [lateBody, arms, armSigs, base, recurse, capturedTarget, capture, counter,
      payload, spare, Code.plan, DemandPlan.prepend, transfer, selectWires, Wires.addresses, Origin.address,
      Demand.observes, Port.index, definedAt,
      demandedRead, h]

private def late : Family Op later single slots [earlyPorts] where
  context := [earlyFn.port, num]
  captures := .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil)
  memberWires i := Fin.cases
    (.cons (.arg (.tail (.tail .head))) (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)))
    (fun j => j.elim0) i
  sigs := fun _ => [decision, single]
  body i := Fin.cases lateBody (fun j => j.elim0) i
  closed := by
    intro i d
    obtain rfl := Fin.eq_zero i
    change (∀ p, p < 1 → Address.arg p ∉ (lateBody.plan d).live) ∧
      ∀ p, Address.arg (1 + p) ∈ (lateBody.plan d).live → Address.arg p ∈ later.live 0 d
    rw [lateReads]
    cases h : d 0 <;> simp [demandedRead, h, List.mem_cons] <;> omega

private def group := GroupBinding.ofFamily late

private def firstScope (cap : Nat) := Scope.seed early (one cap) (one cap)

private theorem lateReady (cap : Nat) :
    late.ReadyWith (group.read (one cap) (firstScope cap).localsL) ((firstScope cap).guardL.combine
      (late.guard (group.read (one cap) (firstScope cap).localsL))) := by
  intro i
  obtain rfl := Fin.eq_zero i
  refine ⟨rfl, ?_⟩
  intro args locals outputs
  refine ⟨?_, fun _ _ _ => trivial⟩
  intro arm
  refine Fin.cases ?_ (fun _ => ?_) arm
  · exact ⟨⟨rfl, rfl⟩, fun _ => trivial⟩
  · exact ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩

private abbrev past := [earlyPorts, latePorts]

private def wrapper : Binding Op slots single past lateFn where
  context := [lateFn.port, earlyFn.port, num]
  captures := .cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil))
  sigs := [single, []]
  body := recurse

private def tail : ModuleTerm Op single [earlyPorts] [latePorts, [lateFn.port]] [lateFn.port] :=
  .bind (.phi group.term) (.bind (.lambda wrapper.term) (.ret (lastExport past lateFn)))

private def numbered := seededGraph early tail
private def finalScope (cap : Nat) := (firstScope cap).addGroup group (one cap) (one cap)

private theorem wrapperReady (cap : Nat) : wrapper.resolved (finalScope cap).guardL (one cap) (finalScope cap).localsL :=
  fun _ _ => ⟨⟨rfl, rfl⟩, fun _ _ => trivial⟩

private def plan (cap : Nat) :
    Plan (one cap) (one cap) (firstScope cap) wrapper.summary tail :=
  .phiWithEarlier (scope := firstScope cap) group (lateReady cap) (lateReady cap)
    (.finish (scope := finalScope cap) wrapper (wrapperReady cap) (wrapperReady cap))

private def admitted (cap : Nat) :=
  (plan cap).analyzeNumbered early actions 83 numbered (one cap) (one cap) 20
    (by exact OmegaTerm.toTerm_toGraph _) (earlyReady cap) (earlyReady cap)

private def analysis (cap : Nat) := (admitted cap).get (by rfl)
private def requested : Demand := (· == 0)
private def noResults : Demand := fun _ => false

#guard (analysis 3).liveCapture noResults (.tail (.tail .head))
#guard (analysis 3).liveFormal noResults .head
#guard (analysis 3).liveFormal requested (.tail .head)
#guard !(analysis 3).liveFormal noResults (.tail .head)
#guard !(analysis 3).liveFormal requested (.tail (.tail .head))

example : Address.arg 4 ∈ ((analysis 3).problem requested).mayOut 0 :=
  ((analysis 3).mem_liveIn_iff requested _).1 (by decide)

example : Address.arg 4 ∉ ((analysis 3).problem noResults).mayOut 0 :=
  fun h => (by decide : Address.arg 4 ∉ (analysis 3).liveIn noResults)
    (((analysis 3).mem_liveIn_iff noResults _).2 h)

private def args (spare : Nat) : Tuple machine.Val lateFn.args :=
  .cons (.data (1 : Nat)) (.cons (.data (41 : Nat)) (one spare))

private def run (fuel cap spare : Nat) :=
  Executable.run actions fuel 83 numbered (one cap) .head (args spare) 20

example (fuel after cap : Nat) :
    ∃ left right, run fuel cap 4 = .ok left ∧ run fuel cap 40 = .ok right ∧
      PrefixObservationsAgree actions requested after left right := by
  obtain ⟨left, right, ranL, ranR, agree⟩ :=
    (analysis cap).linked_substituteDeadFormals requested fuel after (args 4) (args 40) (fun _ _ => rfl)
  have substituted : (analysis cap).substituteDeadFormals requested (args 4) (args 40) = args 40 := rfl
  rw [substituted] at ranR
  exact ⟨left, right, ranL, ranR, agree⟩

private def returned : Observation machine Nat single → Option (Nat × Nat)
  | .returned (.cons (.data payload) .nil) store => some (payload, store)
  | _ => none

private def blocked (spare : Nat) : Option (Nat × Nat) :=
  match run 80 0 spare with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, .cons (.data n) .nil⟩, _⟩ store) => some (n, store)
  | _ => none

private def resumed (spare : Nat) : Option (Nat × Nat) :=
  match run 80 0 spare with
  | .ok (.blocked ⟨⟨_, _, .probe, _, _, _⟩, stack⟩ _) =>
    returned (observe actions (runFor actions 80 ⟨.returned .nil stack, 50⟩))
  | _ => none

#guard (run 80 3 4).toOption.bind returned == some (41, 45)
#guard (run 80 3 40).toOption.bind returned == some (41, 45)
#guard blocked 4 == some (0, 22)
#guard blocked 40 == some (0, 22)
#guard resumed 4 == some (41, 70)
#guard resumed 40 == some (41, 70)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Groups.EarlierRegression
