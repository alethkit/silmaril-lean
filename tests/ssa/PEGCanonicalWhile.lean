module

import Silmaril.SSA.PEG.Simple.Revert.While.Thms
meta import Silmaril.SSA.PEG.Simple.Revert.While.Defs

namespace Silmaril.SSA.PEG.Simple.Revert.While.Tests

open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | nonzero : Op [.count] .bool
  | pred : Op [.count] .count
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .nonzero, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

private def form : Form Op .count := ⟨.nonzero, .pred, .not⟩

private def store (n : Nat) : Tuple model.Value [.count] := .cons ⟨n⟩ .nil

private theorem countDown (n : Nat) :
    Exec model form.program.source.body (store n) (some (store 0)) := by
  induction n with
  | zero => exact .whileStop rfl
  | succ n ih =>
    let assigned := Tuple.cons (F := model.Value) (t := Ty.count) ⟨n⟩ (store (n + 1))
    exact .whileStep (next := store n) rfl (.seq (next := assigned) (.assign rfl) .project) ih

private theorem accepted : ∃ cert, extract form.compile = some cert ∧ cert.form = form :=
  form.compile_extract

-- The extracted SIMPLE loop returns at zero iterations and at arbitrary finite exits.
example (n : Nat) : ∃ cert, extract form.compile = some cert ∧
    cert.revert.Returns model (store n) ⟨0⟩ := by
  obtain ⟨cert, checked, recovered⟩ := accepted
  refine ⟨cert, checked, store 0, ?_, ?_⟩
  · change Exec model cert.form.program.source.body (store n) (some (store 0))
    rw [recovered]
    exact countDown n
  · change (store 0).get cert.form.program.retvar = _
    rw [recovered]
    rfl

example (n : Nat) : ∃ cert, extract form.compile = some cert ∧
    form.compile.observe model (form.compile.denote model (store n) cert.demandWellFounded)
      (fun _ => 19) = .cons (some ⟨0⟩) .nil := by
  obtain ⟨cert, checked, recovered⟩ := accepted
  refine ⟨cert, checked, cert.observe_of_returns model (store n) ?_ ?_ _⟩
  · rw [recovered]
    intro b
    rfl
  · change cert.form.program.source.Returns model (store n) ⟨0⟩
    rw [recovered]
    exact ⟨store 0, countDown n, rfl⟩

-- Pass reads the continuation test directly, bypassing negation. Wiring is
-- still well sorted, but this is a different loop exit.
private def wrongExitRaw : RawGraph Op [.count] [.count] 7 1 :=
  { form.compile.toRaw with node := fun i =>
    let row := form.compile.toRaw.node i
    if i = 1 then { row with args := [4] } else row }

private def wrongExit : Graph Op [.count] [.count] 7 1 := wrongExitRaw.check.get (by decide)

example : extract wrongExit = none := by
  cases h : extract wrongExit with
  | none => rfl
  | some cert =>
    have mismatch := congrArg (fun g : RawGraph Op [.count] [.count] 7 1 =>
      (g.node 1).args) cert.table
    change [4] = [2] at mismatch
    contradiction

set_option interpreter.prefer_native false

/-- info: true -/
#guard_msgs in
#eval (extract form.compile).isSome

/-- info: true -/
#guard_msgs in
#eval (extract wrongExit).isNone

end Silmaril.SSA.PEG.Simple.Revert.While.Tests
