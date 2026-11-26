module

import Silmaril.SSA.PEG.Builder
import Silmaril.SSA.Peggy.Bridge.Egg.Thms
meta import Silmaril.SSA.Peggy.Bridge.Egg.Defs
meta import Silmaril.SSA.Peggy.Acyclic.Defs
meta import Silmaril.Logic.Egg.Core.Replay.Defs
meta import Silmaril.SSA.PEG.Builder

namespace Silmaril.SSA.Peggy.Tests

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Core.Replay (Receipt)
open PEG (Ty RawGraph Graph)
open Acyclic (Interpretation Ranked)
open Bridge.Egg

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | yes : Op [] .bool
  | no : Op [] .bool
  | fail : Op [] .count
  | add : Op [.count, .count] .count
  deriving DecidableEq

private abbrev params : List (Ty Unit) := [.bool, .count, .count]
private abbrev results : List (Ty Unit) := [.count, .count, .count, .bool]

/-- The add uses the selected value twice. The first and third outputs share
the add, and the two count parameters occupy distinct input slots. -/
private def source : RawGraph Op params results 7 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 2 ∨ i = 6 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .op .add, [1, 1]⟩
    | 1 => ⟨_, .phi, [2, 3, 4]⟩
    | 2 => ⟨_, .op .yes, []⟩
    | 3 => ⟨_, .param (.tail .head), []⟩
    | 4 => ⟨_, .op .fail, []⟩
    | 5 => ⟨_, .param (.tail (.tail .head)), []⟩
    | 6 => ⟨_, .param .head, []⟩
  roots := [0, 5, 0, 6]

private def target : RawGraph Op params results 4 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 3 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .param (.tail .head), []⟩
    | 1 => ⟨_, .op .add, [0, 0]⟩
    | 2 => ⟨_, .param (.tail (.tail .head)), []⟩
    | 3 => ⟨_, .param .head, []⟩
  roots := [1, 2, 1, 3]

private def sourceRank (i : Fin 7) : Nat := match i with
  | 0 => 2 | 1 => 1 | _ => 0

private def targetRank (i : Fin 4) : Nat := if i = 1 then 1 else 0

private def src : Graph Op params results 7 0 := source.check.get (by decide)
private def dst : Graph Op params results 4 0 := target.check.get (by decide)
private def srcRanked : Ranked src := (Ranked.check src sourceRank).get (by decide)
private def dstRanked : Ranked dst := (Ranked.check dst targetRank).get (by decide)

-- A well-typed self-edge still fails fragment admission.
private def cyclic : Graph Op params results 7 0 :=
  ({ source with node := fun i => if i = 0 then { source.node i with args := [0, 1] }
    else source.node i }).check.get (by decide)

example : (Ranked.check cyclic sourceRank).isNone = true := by decide

private abbrev T := Term Op params

private def yes : T .bool := .app (.prim Op.yes) (fun j => j.elim0)
private def no : T .bool := .app (.prim Op.no) (fun j => j.elim0)
private def failed : T .count := .app (.prim Op.fail) (fun j => j.elim0)
private def condition : T .bool := .var 0
private def x : T .count := .var 1
private def y : T .count := .var 2

private def phi (c : T .bool) (a b : T .count) : T .count :=
  .app (.phi .count) (fun i => match i with | 0 => c | 1 => a | 2 => b)

private abbrev selectTrue : Core.Rule (signature Op) where
  scope := params.length
  context := context params
  guards := [⟨.bool, condition, yes⟩]
  conclusion := ⟨.count, phi condition x y, x⟩

private abbrev rules := [selectTrue]
private abbrev Rec := Receipt rules (context params)

private def substitute (i : Fin params.length) : T params[i] :=
  match i with | 0 => yes | 1 => x | 2 => failed

private def select (guardReceipt : Rec .bool) : Rec .count :=
  Receipt.rewrite (rs := rules) 0 substitute (fun j : Fin 1 => match j with | 0 => guardReceipt)

private def receipts (guardReceipt : Rec .bool) (i : Fin results.length) : Rec results[i] :=
  let rewrite := select guardReceipt
  let underAdd : Rec .count :=
    .congr (Symbol.prim Op.add) (fun i => match i with | 0 => rewrite | 1 => rewrite)
  match i with
  | 0 => underAdd
  | 1 => .refl y
  | 2 => .trans underAdd (.refl (.app (.prim Op.add) (fun j => match j with | 0 => x | 1 => x)))
  | 3 => .refl condition

private abbrev opEq : PrimitiveEq Op := fun _ _ => inferInstance

#guard (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome
#guard (checkOutputs opEq dstRanked srcRanked (fun i => .symm (receipts (.refl yes) i))).isSome
#guard (checkOutputs opEq srcRanked dstRanked (receipts (.refl no))).isNone
#guard ((Receipt.trans (.refl x) (.refl y) : Rec .count).replay (matchSymbol opEq)).isNone

private def swapped : Graph Op params results 4 0 :=
  ({ target with roots := [2, 1, 1, 3] }).check.get (by decide)

private def swappedRanked : Ranked swapped := (Ranked.check swapped targetRank).get (by decide)

#guard (checkOutputs opEq srcRanked swappedRanked (receipts (.refl yes))).isNone

private def interp : Interpretation Op where
  carrier _ := Unit
  prim
    | .yes, .nil => some true
    | .no, .nil => some false
    | .fail, .nil => none
    | .add, .cons a (.cons b .nil) => some (Nat.add a b)

private def input (i : Fin params.length) : interp.Partial params[i] :=
  match i with | 0 => none | 1 => some (7 : Nat) | 2 => some (3 : Nat)

#guard (show Option Nat from srcRanked.evalOutputs interp input 0) == some 14
#guard (show Option Nat from srcRanked.evalOutputs interp input 1) == some 3
#guard (show Option Nat from srcRanked.evalOutputs interp input 2) == some 14
#guard (srcRanked.evalOutputs interp input 3).isNone
#guard (srcRanked.evalOutputs interp (fun _ => none) 0).isNone

private theorem selectTrue_holds : selectTrue.Holds (model interp) := by
  intro ρ guards
  have hc := guards ⟨.bool, condition, yes⟩ (List.mem_singleton_self _)
  change ρ 0 = some true at hc
  change (ρ 0).bind (fun b : Bool => if b then ρ 1 else ρ 2) = ρ 1
  rw [hc]
  rfl

example (accepted : (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome) :
    srcRanked.evalOutputs interp input = dstRanked.evalOutputs interp input := by
  apply checkOutputs_sound opEq accepted interp _ input
  intro r hr
  have : r = selectTrue := List.mem_singleton.mp hr
  exact this ▸ selectTrue_holds

-- Equal branch values do not justify dropping an undefined control operand.
private def unsafePhi : Core.Rule (signature Op) :=
  { selectTrue with guards := [], conclusion := ⟨.count, phi condition x x, x⟩ }

example : ¬unsafePhi.Holds (model interp) := by
  intro holds
  have eq := holds input (by intro e he; cases he)
  change (none : Option Nat) = some 7 at eq
  cases eq

end Silmaril.SSA.Peggy.Tests
