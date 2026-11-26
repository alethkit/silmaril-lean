module

import Silmaril.SSA.SeaOfNodes.GCM.Hoist.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.Regression

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.Pure (Eval i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Hoist

private def i8 : Width := ⟨8, by decide⟩
private def i16 : Width := ⟨16, by decide⟩

private inductive Op : List Width → Width → Type where
  | add : Op [i8, i8] i8
  | widenAndTriple : Op [i8] i16

private def evalOp : Eval Op :=
  fun op args => match op with
    | .add => (args.get .here) + (args.get (.there .here))
    | .widenAndTriple => (args.get .here).zeroExtend i16.val * 3

private def diamond : Diamond Op [i1, i8, i8, i16, i16, i16] i8 i16 where
  seedTypes := [i8, i8]
  seed := .add
  seedOperands := .cons (.there .here) (.cons (.there (.there .here)) .nil)
  producer := .widenAndTriple
  selector := .here
  fallback := .there (.there (.there .here))
  leftExtra := .there (.there (.there (.there .here)))
  rightExtra := .there (.there (.there (.there (.there .here))))

private abbrev BeforeLabel := Label i8 i16 false

private def address : BlockId BeforeLabel → List Nat
  | none => []
  | some ⟨_, .left⟩ => [0]
  | some ⟨_, .right⟩ => [1]
  | some ⟨_, .join⟩ => [2]

private theorem address_injective {a b : BlockId BeforeLabel} (same : address a = address b) :
    a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [address] at same
  · cases a <;> simp [address] at same
  · cases a <;> cases b <;> simp_all [address]

private theorem prefix_cases {a b : BlockId BeforeLabel}
    (ancestor : (address a).isPrefixOf (address b) = true) : a = none ∨ a = b := by
  rcases a with _ | ⟨_, a⟩
  · exact .inl rfl
  rcases b with _ | ⟨_, b⟩
  · cases a <;> cases ancestor
  · cases a <;> cases b <;> first | exact .inr rfl | cases ancestor

private theorem path_endpoint {b : BlockId BeforeLabel} {past : List (BlockId BeforeLabel)}
    (path : EntryPath diamond.before b past) : b ∈ past := by
  cases path <;> exact List.mem_cons_self

private theorem path_entry {b : BlockId BeforeLabel} {past : List (BlockId BeforeLabel)}
    (path : EntryPath diamond.before b past) : none ∈ past := by
  induction path with
  | entry => exact List.mem_cons_self
  | step _ _ _ ih => exact List.mem_cons_of_mem _ ih

private theorem reachable (b : BlockId BeforeLabel) : Reachable diamond.before b := by
  have left : EntryPath diamond.before (some ⟨_, .left⟩) [leftId, none] := .step .entry .onTrue rfl
  rcases b with _ | ⟨_, label⟩
  · exact ⟨_, .entry⟩
  cases label
  · exact ⟨_, left⟩
  · exact ⟨_, .step .entry .onFalse rfl⟩
  · exact ⟨_, .step left .jump rfl⟩

private def tree : DominatorTree diamond.before where
  address := address
  entry_address := rfl
  address_injective := address_injective
  reachable := fun _ => true
  reachable_sound := fun {b} _ => reachable b
  prefix_sound := by
    intro a b _ ancestor past path
    rcases prefix_cases (List.isPrefixOf_iff_prefix.mpr ancestor) with rfl | rfl
    · exact path_entry path
    · exact path_endpoint path

private theorem picked : diamond.pickAndHoist? tree = some (entryCut, diamond.after) := by cbv

-- The producer moves from the true arm to entry. The right arm and the join
-- remain binding-free in both CFGs.
example : ((shape diamond.before none).bindings, (shape diamond.before leftId).bindings) = (1, 1) := rfl
example : ((shape diamond.after none).bindings,
    (shape diamond.after (some ⟨_, .left⟩)).bindings) = (2, 0) := rfl

example : (Use.phi leftId .jump 0).point? diamond.before = some ⟨leftId, 1⟩ := rfl

private def early : Point BeforeLabel := ⟨none, 0⟩

-- Cut zero is a valid position that dominates the edge use. Adding the
-- real seed definition makes that cut fail the operand check.
example : checkPlacement tree [] useSites early = true := by cbv
example : checkPlacement tree operandSites useSites early = false := by cbv
example : diamond.hoistAt? tree early = none := by cbv

private def inputs (selector : Bool) : Env [i1, i8, i8, i16, i16, i16] :=
  .cons (BitVec.ofBool selector) (.cons 5 (.cons 7 (.cons 93 (.cons 41 (.cons 57 .nil)))))

example :
    diamond.before.entry.eval evalOp (fun term env => term.eval env) (inputs true) =
      .inl (⟨.left, .cons 12 (.cons 41 .nil)⟩ : Frame BeforeLabel) := by cbv

example :
    diamond.after.entry.eval evalOp (fun term env => term.eval env) (inputs true) =
      .inl (⟨.left, .cons 12 (.cons 41 (.cons 36 .nil))⟩ : Frame (Label i8 i16 true)) := by cbv

-- The taken true edge to the join passes the producer's result and its
-- own payload. The false edge passes the fallback and a different payload.
example : diamond.before.run evalOp 3 (inputs true) = some (.cons 36 (.cons 41 .nil)) := by cbv
example : diamond.after.run evalOp 3 (inputs true) = some (.cons 36 (.cons 41 .nil)) := by cbv
example : diamond.before.run evalOp 3 (inputs false) = some (.cons 93 (.cons 57 .nil)) := by cbv
example : diamond.after.run evalOp 3 (inputs false) = some (.cons 93 (.cons 57 .nil)) := by cbv
example : diamond.after.run evalOp 2 (inputs true) = none := by cbv

example (selector : Bool) (result : Env [i16, i16]) :
    (∃ fuel, diamond.before.run evalOp fuel (inputs selector) = some result) ↔
      ∃ fuel, diamond.after.run evalOp fuel (inputs selector) = some result :=
  pickAndHoist?_returns_iff picked evalOp (inputs selector) result

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Hoist.Regression
