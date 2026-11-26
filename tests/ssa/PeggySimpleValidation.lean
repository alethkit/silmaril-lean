module

import Silmaril.SSA.Peggy.SimpleValidation.Thms
meta import Silmaril.SSA.Peggy.SimpleValidation.Defs
meta import Silmaril.SSA.PEG.Defs

namespace Silmaril.SSA.Peggy.SimpleValidation.Tests

open PEG (Ty)
open PEG.Simple (Expr Stmt)
open Bridge.Egg (Term PrimitiveEq context model)
open Bridge.Figure11 (toAcyclic)
open Optimizer (Rule)
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | add : Op [.count, .count] .count
  | triple : Op [.count] .count
  | bad : Op [] .count
  deriving DecidableEq

private def arithmetic : PEG.Interpretation Op where
  carrier _ := Unit
  run
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .triple, .cons a .nil => some ⟨(a.down + a.down) + a.down⟩
    | .bad, .nil => none

private abbrev params : List (Ty Unit) := [.bool, .count]
private abbrev input (flag : Bool) (n : Nat) : Tuple arithmetic.Value params :=
  .cons ⟨flag⟩ (.cons ⟨n⟩ .nil)

private def plus {vars : List (Ty Unit)} (a b : Expr Op vars .count) : Expr Op vars .count :=
  .op .add (.cons a (.cons b .nil))

private def trueArm : Stmt Op false params [.count] :=
  let x := Expr.var (.tail .head)
  .seq (.assign (plus (plus x x) x))
    (.seq (.assign (plus (.var .head) (.var .head))) (.project (.cons .head .nil)))

/-- The true arm uses its computed triple twice. The false arm fails. -/
private def source : PEG.Simple.Program Op false params .count :=
  ⟨[.count],
    .branch (.var .head) trueArm (.seq (.assign (.op .bad .nil)) (.project (.cons .head .nil))),
    .head⟩

private abbrev pattern : List (Ty Unit) := [.count]

private def addPattern (a b : Term Op pattern .count) : Term Op pattern .count :=
  .app (.prim Op.add) (fun i => match i with | 0 => a | 1 => b)

private def compress : Rule Op .count :=
  let x : Term Op pattern .count := .var 0
  { scope := pattern.length
    context := context pattern
    guards := []
    lhs := addPattern (addPattern x x) x
    rhs := .app (.prim Op.triple) (fun i => match i with | 0 => ⟨0, rfl⟩) }

private def rules : List (Optimizer.Contextual.Schema Op) := [⟨.count, compress⟩]
private abbrev opEq : PrimitiveEq Op := fun _ _ => inferInstance

private def addValues (a b : Option Nat) : Option Nat :=
  (toAcyclic arithmetic).applyPrim Op.add (fun i => match i with | 0 => a | 1 => b)

private def tripleValue (value : Option Nat) : Option Nat :=
  (toAcyclic arithmetic).applyPrim Op.triple (fun i => match i with | 0 => value)

/-- Includes the substitution assigning bottom to x. -/
private theorem compressLaw : compress.core.Holds (model (toAcyclic arithmetic)) := by
  intro ρ _
  let v : Option Nat := ρ (show Fin pattern.length from 0)
  change addValues (addValues v v) v = tripleValue v
  cases v <;> rfl

private theorem rulesSound : ∀ rule ∈ rules.map Optimizer.Contextual.core,
    rule.Holds (model (toAcyclic arithmetic)) := by
  intro rule mem
  have h : rule = compress.core := List.mem_singleton.mp mem
  exact h ▸ compressLaw

private def answer (n : Nat) : Nat :=
  let y := (n + n) + n
  y + y

private theorem sourceReturns (n : Nat) : source.Returns arithmetic (input true n) ⟨answer n⟩ := by
  let afterTriple : Tuple arithmetic.Value (.count :: params) := .cons ⟨(n + n) + n⟩ (input true n)
  let afterSum : Tuple arithmetic.Value (.count :: .count :: params) :=
    .cons ⟨answer n⟩ afterTriple
  refine ⟨.cons ⟨answer n⟩ .nil, ?_, rfl⟩
  exact .branchTrue rfl
    (.seq (next := afterTriple) (.assign rfl)
      (.seq (next := afterSum) (.assign rfl) .project))

example (accepted : Accepted source rules) (n : Nat) :
    accepted.output.runLoopFree arithmetic (input true n) = some ⟨answer n⟩ :=
  accepted.runLoopFree arithmetic rulesSound _ (sourceReturns n)

private def opName {ins : List (Ty Unit)} {out : Ty Unit} : Op ins out → String
  | .add => "add"
  | .triple => "triple"
  | .bad => "bad"

private def assignedOps : {vars outs : List (Ty Unit)} → Stmt Op false vars outs → List String
  | _, _, .assign (.op op _) => [opName op]
  | _, _, .assign (.var _) | _, _, .project _ => []
  | _, _, .seq a b => assignedOps a ++ assignedOps b
  | _, _, .branch _ yes no => assignedOps yes ++ assignedOps no
  | _, _, .while impossible _ _ => nomatch impossible

private def report (depth : Nat) (flag : Bool) :
    Except Rejection (Nat × Nat × List String × Option Nat) := do
  let accepted ← optimize opEq rules depth source
  let before := Optimizer.Contextual.cost ⟨_, source.translate, accepted.ranked⟩
  let after := Optimizer.Contextual.cost accepted.candidate.program
  return (before, after, assignedOps accepted.output.body,
    (accepted.output.runLoopFree arithmetic (input flag 14)).map ULift.down)

set_option interpreter.prefer_native false

/-- info: Except.ok (5, 5, ["add", "add", "add", "bad"], some 84) -/
#guard_msgs in
#eval report 0 true

-- The rule matches inside the selected arm, below the shared sum and its enclosing φ.
/-- info: Except.ok (5, 4, ["triple", "add", "bad"], some 84) -/
#guard_msgs in
#eval report 1 true

/-- info: Except.ok (5, 4, ["triple", "add", "bad"], none) -/
#guard_msgs in
#eval report 1 false

/-- Both arms read the same previously computed value. The current
scheduler would duplicate its writer and rejects this placement. -/
private def sharedArms : PEG.Simple.Program Op false params .count :=
  ⟨[.count], .seq (.assign (.op .triple (.cons (.var (.tail .head)) .nil)))
    (.branch (.var (.tail .head)) (.project (.cons .head .nil)) (.project (.cons .head .nil))),
    .head⟩

private def rejected : Option Rejection :=
  match optimize opEq [] 0 sharedArms with
  | .ok _ => none
  | .error error => some error

/-- info: some (Silmaril.SSA.Peggy.SimpleValidation.Rejection.reversion) -/
#guard_msgs in
#eval rejected

end Silmaril.SSA.Peggy.SimpleValidation.Tests
