module

import Silmaril.SSA.PEG.Builder
import Silmaril.SSA.PEG.Simple.Revert.Automatic.Thms
meta import Silmaril.SSA.PEG.Simple.Revert.Automatic.Defs
meta import Silmaril.SSA.PEG.Builder
meta import Silmaril.SSA.PEG.Defs

namespace Silmaril.SSA.PEG.Simple.Revert.Tests

open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | add : Op [.count, .count] .count
  | divide : Op [.count] .count
  | bad : Op [] .count

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .divide, .cons a .nil => if a.down = 0 then none else some ⟨12 / a.down⟩
    | .bad, .nil => none

private def input (flag : Bool) (x : Nat) : Tuple model.Value [.bool, .count] :=
  .cons ⟨flag⟩ (.cons ⟨x⟩ .nil)

/-- The root is add(φ(flag, doubled, divide(x)), doubled).
The doubled node uses the same input twice. Vertex 3 is dead and partial. -/
private def raw (resultArgs : List Nat) (deadArgs : Option (List Nat) := none)
    (yesNode : Nat := 4) :
    RawGraph Op [.bool, .count] [.count] 7 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 5 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .op .add, resultArgs⟩
    | 1 => ⟨_, .op .divide, [2]⟩
    | 2 => ⟨_, .param (.tail .head), []⟩
    | 3 => match deadArgs with
      | none => ⟨_, .op .bad, []⟩
      | some args => ⟨_, .op .add, args⟩
    | 4 => ⟨_, .op .add, [2, 2]⟩
    | 5 => ⟨_, .param .head, []⟩
    | 6 => ⟨_, .phi, [5, yesNode, 1]⟩
  roots := [0]

private def graph : Graph Op [.bool, .count] [.count] 7 0 := (raw [6, 4]).check.get (by decide)

private def rank : Fin 7 → Nat
  | 0 => 3
  | 4 | 1 => 1
  | 6 => 2
  | _ => 0

private def prefixPlan (next : Plan 7) : Plan 7 :=
  .reveal 0 (.reveal 4 (.reveal 6 (.bind 5 (.bind 2 (.bind 4 next)))))

private def plan : Plan 7 :=
  prefixPlan (.branch 6 .done (.bind 1 .done) (.bind 0 .done))

private def accepted : Certificate graph := (Certificate.check graph rank plan).get (by decide)

example : DepthZero graph 0 := accepted.depthZero 0

example : accepted.schedule.bindings = [5, 2, 4, 6, 1, 0] := by decide

-- Both partial vertices are bottom here. The selected path still returns.
example : accepted.revert.runLoopFree model (input true 0) = some ⟨0⟩ := rfl

example : accepted.revert.runLoopFree model (input true 3) = some ⟨12⟩ := rfl
example : accepted.revert.runLoopFree model (input false 3) = some ⟨10⟩ := rfl
example : accepted.revert.runLoopFree model (input false 0) = none := by decide

-- Reject speculation of the false arm, even though its inputs are available.
example : (Certificate.check graph rank
    (prefixPlan (.bind 1 (.branch 6 .done .done (.bind 0 .done))))).isNone = true := by decide

-- Reject an arm missing its selected operand and a consumer scheduled before its operand.
example : (Certificate.check graph rank
    (prefixPlan (.branch 6 .done .done (.bind 0 .done)))).isNone = true := by
  decide
example : (Certificate.check graph rank
    (.reveal 0 (.reveal 4 (.bind 4 (.bind 2 plan))))).isNone = true := by decide

-- The local checks alone allow a repeated binding. Admission rejects it.
private def duplicate : Plan 7 :=
  prefixPlan (.branch 6 (.bind 4 .done) (.bind 1 .done) (.bind 0 .done))

example : (duplicate.check graph (returnRef graph) [] [0]).isSome = true := by decide
example : (Certificate.check graph rank duplicate).isNone = true := by decide

-- Vertex 1 is demanded by the continuation but is bound only in the false arm.
private def escapeRaw : RawGraph Op [.bool, .count] [.count] 7 0 :=
  raw [6, 1]

private def escapePlan : Plan 7 :=
  .reveal 0 (.reveal 1 (.reveal 6
    (.bind 5 (.bind 2 (.branch 6 (.reveal 4 (.bind 4 .done)) (.bind 1 .done) (.bind 0 .done))))))

example : (Certificate.check (escapeRaw.check.get (by decide)) rank escapePlan).isNone = true := by
  decide

private def deadCycle : RawGraph Op [.bool, .count] [.count] 7 0 :=
  raw [6, 4] (some [3, 3])

example : (Certificate.check (deadCycle.check.get (by decide)) rank plan).isNone = true := by
  decide

-- Check the public return theorem against the Figure 11 observation of a
-- small builder graph whose unselected branch is bottom.
private def lazyCode : Code Op [.bool, .count] [] [.count, .count, .count, .bool] :=
  .emit (.emit (.emit (.emit .empty (.param .head) .nil) (.param (.tail .head)) .nil) (.op .bad) .nil)
    .phi (.cons (.tail (.tail .head)) (.cons (.tail .head) (.cons .head .nil)))

private def lazyGraph : Graph Op [.bool, .count] [.count] 4 0 :=
  lazyCode.toGraph (.cons .head .nil)

private def lazyPlan : Plan 4 :=
  .reveal 0 (.bind 3 (.branch 0 (.bind 2 .done) (.bind 1 .done) .done))

private def lazyCert : Certificate lazyGraph :=
  (Certificate.check lazyGraph (fun i => 3 - i.val) lazyPlan).get (by decide)

example : lazyCert.revert.runLoopFree model (input true 19) = some ⟨19⟩ := by
  apply lazyCert.revert_run model (input true 19) Index.zero
  unfold lazyGraph
  rw [Code.observe_toGraph]
  rfl

set_option interpreter.prefer_native false

-- Inference supplies both the rank and the scoped schedule for the diamond.
/-- info: some [5, 2, 4, 6, 1, 0] -/
#guard_msgs in
#eval (Automatic.check graph).map (fun cert => cert.schedule.bindings.map Fin.val)

private def autoRun (flag : Bool) (x : Nat) : Option Nat := do
  let cert ← Automatic.check graph
  (cert.revert.runLoopFree model (input flag x)).map ULift.down

/-- info: some 0 -/
#guard_msgs in
#eval autoRun true 0

/-- info: some 10 -/
#guard_msgs in
#eval autoRun false 3

/-- info: none -/
#guard_msgs in
#eval autoRun false 0

private def sharedArms : Graph Op [.bool, .count] [.count] 7 0 :=
  (raw [6, 4] none 1).check.get (by decide)

-- The planner leaves each demand in its arm. The checker rejects the duplicated division.
/-- info: (true, true) -/
#guard_msgs in
#eval ((Automatic.plan sharedArms rank).isSome, (Automatic.checkRanked sharedArms rank).isNone)

/-- info: true -/
#guard_msgs in
#eval (Automatic.check (deadCycle.check.get (by decide))).isNone

private def straightCode : Code Op [.bool, .count] [] [.count, .count, .count] :=
  .emit (.emit (.emit .empty (.param (.tail .head)) .nil) (.op .bad) .nil) (.op .add)
    (.cons (.tail .head) (.cons (.tail .head) .nil))

private def straightGraph : Graph Op [.bool, .count] [.count] 3 0 :=
  straightCode.toGraph (.cons .head .nil)

private def straightRank (i : Fin 3) : Nat := 2 - i.val

private def straightCert : Certificate straightGraph :=
  (Automatic.check straightGraph).get
    (Automatic.check_accepts_straightLine straightGraph straightRank
      (by unfold Automatic.StraightLine; decide) (by decide))

/-- info: some 10 -/
#guard_msgs in
#eval (straightCert.revert.runLoopFree model (input false 5)).map ULift.down

end Silmaril.SSA.PEG.Simple.Revert.Tests
