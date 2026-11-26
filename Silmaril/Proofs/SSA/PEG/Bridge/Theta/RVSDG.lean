module

public import Silmaril.SSA.PEG.Bridge.Theta.Defs
public import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
public import Silmaril.SSA.RVSDG.Theta.Thms
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Proofs

open RVSDG (Tuple)
open Silmaril.SSA.PEG.Bridge.Theta.Compiler

variable {Data : Type} {P : InstructionSet.{0,0} Data} {a b : Ty Data}
variable (loop : Loop P a b) (m : TotalModel P)

/-- The actual numbered body tests the old state. On exit, its child
returns that state; on continue, its child reads the same arguments twice. -/
theorem body_run (input : Tuple m.toPEG.Value [a, b]) :
    loop.toTheta.body.run (model m a b) (encodeCarried m input) =
      RVSDG.Theta.bodyResult (model m a b) (!(loop.exits m input))
        (encodeCarried m (if loop.exits m input then input else loop.advance m input)) := by
  change (loop.toThetaTerm.body.toGraph).run (model m a b) _ = _
  rw [RVSDG.Term.run_toGraph]
  cases input with | cons x tail =>
  cases tail with | cons y tail =>
  cases tail
  let xs : Tuple m.toPEG.Value [a, b] := .cons x (.cons y .nil)
  let tag : Fin 2 := if loop.exits m xs then 0 else 1
  let branch (j : Fin 2) := (selectedArm loop j).run (model m a b) (encodeCarried m xs)
  change Tuple.cons (F := (model m a b).Val) (t := .control 2) (ULift.up tag)
    (.cons ((branch tag).get .head) (.cons ((branch tag).get (.tail .head)) .nil)) =
    RVSDG.Theta.bodyResult (model m a b) (!(loop.exits m xs))
      (encodeCarried m (if loop.exits m xs then xs else loop.advance m xs))
  unfold tag
  cases loop.exits m xs <;> rfl

private theorem bodyResult_inj {first second : Tuple m.toPEG.Value [a, b]}
    {flag flag' : Bool} (eq : RVSDG.Theta.bodyResult (model m a b) flag (encodeCarried m first) =
      RVSDG.Theta.bodyResult (model m a b) flag' (encodeCarried m second)) :
    flag = flag' ∧ first = second := by
  have tag := congrArg (fun xs : Tuple (model m a b).Val (RVSDG.Theta.BodyResults (Carried a b)) =>
    (xs.get .head).down.val) eq
  have payload := congrArg
    (fun xs : Tuple (model m a b).Val (RVSDG.Theta.BodyResults (Carried a b)) =>
      fromPorts [a, b] (match xs with | .cons _ ys => ys)) eq
  have firstRound := from_toPorts (F := (model m a b).Val) first
  have secondRound := from_toPorts (F := (model m a b).Val) second
  refine ⟨?_, firstRound.symm.trans (payload.trans secondRound)⟩
  cases flag <;> cases flag' <;> first | rfl | contradiction

private theorem body_step (input output : Tuple m.toPEG.Value [a, b]) (again : Bool) :
    loop.toTheta.body.run (model m a b) (encodeCarried m input) =
      RVSDG.Theta.bodyResult (model m a b) again (encodeCarried m output) ↔
      again = !(loop.exits m input) ∧ output = if again then loop.advance m input else input := by
  rw [body_run]
  constructor
  · intro h
    obtain ⟨flag, payload⟩ := bodyResult_inj m h
    refine ⟨flag.symm, ?_⟩
    rw [← flag, ← payload]
    cases loop.exits m input <;> rfl
  · rintro ⟨rfl, rfl⟩
    cases loop.exits m input <;> rfl

private theorem firstExit_succ (input : Tuple m.toPEG.Value [a, b]) (k : Nat) :
    loop.FirstExit m input (k + 1) ↔
      loop.exits m input = false ∧ loop.FirstExit m (loop.advance m input) k := by
  constructor
  · intro h
    refine ⟨h.2 0 (Nat.zero_lt_succ k), h.1, ?_⟩
    intro j hj
    exact h.2 (j + 1) (Nat.succ_lt_succ hj)
  · rintro ⟨first, next⟩
    refine ⟨next.1, ?_⟩
    intro j hj
    cases j with
    | zero => exact first
    | succ j => exact next.2 j (Nat.lt_of_succ_lt_succ hj)

private theorem exists_exit_of_iterate
    {start finish : Tuple (model m a b).Val (Carried a b)}
    (execution : loop.toTheta.Returns (model m a b) start finish) :
    ∃ k, loop.FirstExit m (fromPorts [a, b] start) k ∧
      fromPorts [a, b] finish = loop.stateAt m k (fromPorts [a, b] start) := by
  change RVSDG.Theta.Iterate _ start finish at execution
  induction execution with
  | @stop start finish completed =>
    have step := (body_step loop m (fromPorts [a, b] start) (fromPorts [a, b] finish) false).mp
      (by simpa only [encodeCarried, to_fromPorts] using completed)
    have exits : loop.exits m (fromPorts [a, b] start) = true := by
      have h := step.1
      exact (show ∀ x : Bool, false = !x → x = true by decide) _ h
    exact ⟨0, ⟨exits, fun j h => (Nat.not_lt_zero j h).elim⟩, step.2⟩
  | @again start next finish completed _ ih =>
    have step := (body_step loop m (fromPorts [a, b] start) (fromPorts [a, b] next) true).mp
      (by simpa only [encodeCarried, to_fromPorts] using completed)
    have continues : loop.exits m (fromPorts [a, b] start) = false := by
      have h := step.1
      exact (show ∀ x : Bool, true = !x → x = false by decide) _ h
    have nextState : fromPorts [a, b] next = loop.advance m (fromPorts [a, b] start) := step.2
    obtain ⟨k, first, output⟩ := ih
    rw [nextState] at first output
    exact ⟨k + 1, (firstExit_succ loop m _ k).mpr ⟨continues, first⟩, output⟩

private theorem returns_at_exit (input : Tuple m.toPEG.Value [a, b]) (k : Nat)
    (first : loop.FirstExit m input k) :
    loop.toTheta.Returns (model m a b) (encodeCarried m input) (encodeCarried m (loop.stateAt m k input)) := by
  induction k generalizing input with
  | zero =>
    apply RVSDG.Theta.Iterate.stop
    have stop : loop.exits m input = true := first.1
    exact (body_step loop m input input false).mpr ⟨by rw [stop]; rfl, rfl⟩
  | succ k ih =>
    obtain ⟨continues, first⟩ := (firstExit_succ loop m input k).mp first
    apply RVSDG.Theta.Iterate.again (next := encodeCarried m (loop.advance m input))
    · exact (body_step loop m input _ true).mpr ⟨by rw [continues]; rfl, rfl⟩
    · exact ih (loop.advance m input) first

theorem returns_iff_firstExit (input output : Tuple m.toPEG.Value [a, b]) :
    loop.toTheta.Returns (model m a b) (encodeCarried m input) (encodeCarried m output) ↔
      ∃ k, loop.FirstExit m input k ∧ output = loop.stateAt m k input := by
  constructor
  · intro h
    have hi := from_toPorts (F := (model m a b).Val) input
    have ho := from_toPorts (F := (model m a b).Val) output
    obtain ⟨k, first, eq⟩ := exists_exit_of_iterate loop m h
    exact ⟨k, hi ▸ first, ho.symm.trans (eq.trans (congrArg (loop.stateAt m k) hi))⟩
  · rintro ⟨k, first, rfl⟩
    exact returns_at_exit loop m input k first

end Silmaril.SSA.PEG.Bridge.Theta.Proofs
