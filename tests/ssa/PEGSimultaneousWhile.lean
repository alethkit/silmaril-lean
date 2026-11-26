module

import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Thms
import Silmaril.SSA.PEG.Simple.Thms
meta import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Defs

namespace Silmaril.SSA.PEG.Simple.Revert.While.Pair.Tests

open RVSDG (Tuple)

private abbrev acc : Ty Unit := .data ()

private inductive Op : InstructionSet Unit where
  | positive : Op [.count] .bool
  | pred : Op [.count] .count
  | addOld : Op [.count, acc] acc
  | bad : Op [.count, acc] acc
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Nat
  run
    | .positive, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .addOld, .cons n (.cons a .nil) => some ((show Nat from a) + n.down)
    | .bad, _ => none
    | .not, .cons flag .nil => some ⟨!flag.down⟩

private def input (n a : Nat) : Tuple model.Value [.count, acc] := .cons ⟨n⟩ (.cons a .nil)

private def sum : Form Op .count acc acc := ⟨.positive, .pred, .addOld, .not, .tail .head⟩

private theorem sumTotal : sum.Total model where
  guard x := ⟨x.down != 0, rfl⟩
  leftStep x := ⟨⟨x.down - 1⟩, rfl⟩
  rightStep store := by
    cases store with | cons n tail =>
    cases tail with | cons a tail =>
    cases tail
    exact ⟨(show Nat from a) + n.down, rfl⟩

private def runExtracted (fuel n a : Nat) : Option Nat := do
  let cert ← extract sum.compile
  cert.form.runFuel model fuel (input n a)

set_option interpreter.prefer_native false

-- The additions see 3, 2 and 1, even though the counter is assigned first.
/-- info: some 16 -/
#guard_msgs in
#eval runExtracted 3 3 10

/-- info: some 10 -/
#guard_msgs in
#eval runExtracted 0 0 10

/-- info: none -/
#guard_msgs in
#eval runExtracted 2 3 10

private theorem sumPeg :
    sum.compile.observe model
      (sum.compile.denote model (input 3 10) (sum.program.translate_demandWellFounded sum.negate))
      (fun _ => 17) = .cons (some (16 : Nat)) .nil :=
  sum.program.translate_returns sum.negate model (input 3 10) (fun _ => rfl)
    (sum.runFuel_returns model 3 (input 3 10) (value := (16 : Nat)) rfl) (fun _ => 17)

private def sumCertificate : Certificate sum.compile := ⟨sum, rfl⟩

example : sumCertificate.revert.Returns model (input 3 10) (16 : Nat) :=
  sumCertificate.returns_of_defined model (input 3 10) sumTotal (fun _ => rfl) _ sumPeg

example : ∃ k, sumCertificate.form.runFuel model k (input 3 10) = some (16 : Nat) := by
  obtain ⟨k, returned, _⟩ :=
    sumCertificate.runFuel_of_defined model (input 3 10) sumTotal (fun _ => rfl) _ sumPeg
  exact ⟨k, returned⟩

-- The right update reads the newly computed left value. This wire is well
-- typed but changes a simultaneous update into a sequential dependency.
private def sequentialRaw : RawGraph Op [.count, acc] [acc] 10 1 :=
  { sum.compile.toRaw with node := fun i =>
    let row := sum.compile.toRaw.node i
    if i = 3 then { row with args := [4, 7] } else row }

private def sequential : Graph Op [.count, acc] [acc] 10 1 :=
  sequentialRaw.check.get (by decide)

/-- info: true -/
#guard_msgs in
#eval (extract sequential).isNone

/-- Left is the only observed slot. The partial right update is still
executed by SIMPLE on a continuing iteration. -/
private def discarded : Form Op .count acc .count := ⟨.positive, .pred, .bad, .not, .head⟩

private theorem notTotal : ¬ discarded.Total model := by
  intro total
  obtain ⟨x, impossible⟩ := total.rightStep (input 1 10)
  cases impossible

private def runDiscarded : Option Nat := do
  let cert ← extract discarded.compile
  (cert.form.runFuel model 1 (input 1 10)).map ULift.down

/-- info: (true, none) -/
#guard_msgs in
#eval ((extract discarded.compile).isSome, runDiscarded)

private def tick (n : Nat) : Index 1 := fun _ => n

private theorem setTick (idx : Index 1) (n : Nat) : idx.set 0 n = tick n := by
  funext i
  have h : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Index.set, tick]

private theorem collectOne {t : Ty Unit}
    (sample : (i : Fin [t].length) → Option (model.Value [t][i])) :
    collect [t] sample = (sample 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases sample 0 <;> rfl

-- Only the left carried stream, unary guard and exit test are demanded.
-- The PEG can return despite the failed right update in the SIMPLE body.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
private theorem discardedPeg :
    discarded.compile.observe model
      (discarded.compile.denote model (input 1 10)
        (discarded.program.translate_demandWellFounded discarded.negate)) (tick 0) =
      .cons (some ⟨0⟩) .nil := by
  let wf := discarded.program.translate_demandWellFounded discarded.negate
  let values := discarded.compile.denote model (input 1 10) wf
  have eq (v : Fin 10) (idx : Index 1) :
      values (v, idx) = discarded.compile.equation model (input 1 10) values (v, idx) :=
    discarded.compile.denote_solves model (input 1 10) wf (v, idx)
  have initial : values (6, tick 0) = some ⟨1⟩ := by
    rw [eq 6 (tick 0)]
    change values (8, tick 0) = _
    exact eq 8 (tick 0)
  have update : values (4, tick 0) = some ⟨0⟩ := by
    rw [eq 4 (tick 0)]
    change (collect [.count] _).elim none (model.run Op.pred) = _
    rw [collectOne]
    change ((values (6, tick 0)).map (fun x => Tuple.cons x .nil)).elim none (model.run Op.pred) = _
    rw [initial]
    rfl
  have next : values (6, tick 1) = some ⟨0⟩ := by
    rw [eq 6 (tick 1)]
    change values (4, (tick 1).set 0 0) = _
    rw [setTick, update]
  have exit (idx : Index 1) (n : Nat) (value : values (6, idx) = some ⟨n⟩) :
      values (2, idx) = some ⟨!(n != 0)⟩ := by
    have guard : values (5, idx) = some ⟨n != 0⟩ := by
      rw [eq 5 idx]
      change (collect [.count] _).elim none (model.run Op.positive) = _
      rw [collectOne]
      change ((values (6, idx)).map (fun x => Tuple.cons x .nil)).elim none
        (model.run Op.positive) = _
      rw [value]
      rfl
    rw [eq 2 idx]
    change (collect [.bool] _).elim none (model.run Op.not) = _
    rw [collectOne]
    change ((values (5, idx)).map (fun x => Tuple.cons x .nil)).elim none (model.run Op.not) = _
    rw [guard]
    rfl
  let flags := fun k => (values (2, tick k)).map ULift.down
  have stop : flags 1 = some true := by
    unfold flags
    rw [exit (tick 1) 0 next]
    rfl
  have again : flags 0 = some false := by
    unfold flags
    rw [exit (tick 0) 1 initial]
    rfl
  have first : firstTrue flags = some 1 := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨stop, ?_⟩, ?_⟩
    · intro j h
      have zj : j = 0 := by omega
      rw [zj, again]
      rfl
    · intro j h hit
      have zj : j = 0 := by omega
      have trueSample := ((monotonize_eq_some_iff _ _ _).mp hit).1
      rw [zj, again] at trueSample
      cases trueSample
  have pass : values (1, tick 0) = some ⟨1⟩ := by
    rw [eq 1 (tick 0)]
    change (firstTrue (fun k => (values (2, (tick 0).set 0 k)).map ULift.down)).map ULift.up = _
    have aligned : (fun k => (values (2, (tick 0).set 0 k)).map ULift.down) = flags := by
      funext k
      exact congrArg (fun idx => (values (2, idx)).map ULift.down) (setTick (tick 0) k)
    rw [aligned, first]
    rfl
  change Tuple.cons (F := fun t => Option (model.Value t)) (values (0, tick 0)) .nil = _
  congr 1
  rw [eq 0 (tick 0)]
  change (values (1, tick 0)).elim none (fun count =>
    monotonize (fun j => values (6, (tick 0).set 0 j)) count.down) = _
  rw [pass]
  change monotonize (fun j => values (6, (tick 0).set 0 j)) 1 = _
  have aligned : (fun j => values (6, (tick 0).set 0 j)) = (fun j => values (6, tick j)) := by
    funext j
    exact congrArg (fun idx => (show Option (model.Value .count) from values (6, idx)))
      (setTick (tick 0) j)
  rw [aligned]
  apply (monotonize_eq_some_iff _ _ _).mpr
  refine ⟨next, fun j lt => ?_⟩
  have zj : j = 0 := by omega
  rw [zj, initial]
  rfl

private theorem discardedFails : discarded.program.source.Fails model (input 1 10) := by
  let updated : Tuple model.Value [.count, .count, acc] := .cons ⟨0⟩ (input 1 10)
  exact .whileBodyFailed rfl (.seq (next := updated) (.assign rfl) (.firstFailed (.assignFailed rfl)))

example : ¬ discarded.program.source.Returns model (input 1 10) ⟨0⟩ := by
  intro success
  obtain ⟨_, ran, _⟩ := success
  cases Exec.deterministic ran discardedFails

end Silmaril.SSA.PEG.Simple.Revert.While.Pair.Tests
