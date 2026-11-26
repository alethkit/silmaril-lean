module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg WordOp model word)
open Silmaril.SSA.RVSDG (Origin)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (encodeTuple inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev scheduleSigs := [[wordPort], [wordPort], [.value .predicate]]

private def oldPort (slot : Fin 4) := suffixPort (wordPorts 4) (argumentPort 4 slot)

private def schedule (lhs : Origin (bankArgs 4) [] wordPort) :
    Dataflow WordOp (bankArgs 4) [] scheduleSigs :=
  .cons .add (.cons lhs (.cons (.arg (oldPort 1)) .nil))
    (.cons .sub (.cons (.arg (oldPort 2)) (.cons (.arg (oldPort 0)) .nil))
      (.cons .slt (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)) .nil))

-- Isolate Simple chapter 13's continuation test (arg + 79) < (32 - arg)
-- in one native loop. Inputs supply both offsets. The left result updates
-- arg, and the right result is available to both feedback and exit.
private def source : BankGraph 4 scheduleSigs where
  preheader := .nil
  header := schedule (.arg (oldPort 0))
  phiInputs
    | .entry => .cons (.arg (argumentPort 4 0)) (.cons (.arg (argumentPort 4 2))
        (.cons (.arg (argumentPort 4 1)) (.cons (.arg (argumentPort 4 3)) .nil)))
    | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.arg (oldPort 1))
        (.cons (.arg (oldPort 2)) (.cons (.output (1 : Fin 3) .head) .nil)))
  predicate := .output (2 : Fin 3) .head
  result := .output (1 : Fin 3) .head

private def spec : Spec where
  entry := [0, 2, 1, 3]
  copies := [0, 1, 2, 3]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 3, 2, 0⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .slt
  limit := 0
  guardRhs := some (.output 1 0)
  exitSlot := 3
  exitOrigin := some (.output 1 0)

private theorem recognized : recognize source = some spec := by cbv

-- The captured argument equals the old bank value on entry, but not
-- after feedback. A typed external reference is not an old-bank producer input.
example : lowerChecked { source with header := schedule (.arg .head) } = none := by cbv

private def duplicateFeedback : BankGraph 4 scheduleSigs :=
  { source with
    phiInputs
      | .entry => source.phiInputs .entry
      | .backedge => .cons (.output (0 : Fin 3) .head) (.cons (.output (0 : Fin 3) .head)
          (.cons (.arg (oldPort 2)) (.cons (.output (1 : Fin 3) .head) .nil))) }

example : lowerChecked duplicateFeedback = none := by cbv

example : (lowerChecked { source with result := .arg (oldPort 3) }).isSome = true := by cbv

private def targets : Checked.Phi.Targets := (lowerBank source, Generic.lower source)
private theorem accepted : lowerChecked source = some targets := by cbv

example : (targets.1.block? 0 1).map (·.ops) = some
    [.binary .add (.node 0) (.arg 4) (.arg 5), .binary .sub (.node 1) (.arg 6) (.arg 4),
     .binary (.cmp .lts) (.node 2) (.node 0) (.node 1)] := by cbv

example : (targets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 0, .arg 2, .arg 1, .arg 3]) := by cbv
example : (targets.1.block? 0 1).map (·.term) =
    some (.cond (.node 2) 1 [.node 0, .arg 5, .arg 6, .node 1] 2 [.node 1]) := by cbv

private def bank (x a b r : Word) : WordTuple 4 := .cons x (.cons a (.cons b (.cons r .nil)))
private def input := bank (-80) 32 79 0
private def spin := bank (-1) 0 0 1
private def mem := Memory.ofList 4 [29, 71, 53, 11]

-- The first test is -1 < 112. Both unsigned and reversed comparisons
-- would exit with 112 immediately. The next test, 78 < 33, exits with 33.
private theorem returns : source.Returns model input (33 : Word) :=
  ⟨1, .backedge (next := bank (-1) 79 32 112) (by cbv) (.exit (by cbv))⟩

example {p : Plan 4} (checked : Rows.checkPlan 4 spec = some p) (frame : Frame Reg)
    (agree : ArgsMatch frame (appendTuple (source.initial model input) input)) :
    Eval (instruction model)
      (extend (inputEnv model input) (encodeTuple model (source.initial model input)))
      (Generic.header source) mem 0 (encodeTuple model (bank (-1) 79 32 112)) mem := by
  have activation := activation_agrees recognized checked input (source.initial model input) frame mem agree
  have taken : source.step model input (source.initial model input) = .inr (bank (-1) 79 32 112) := by cbv
  rw [taken] at activation
  exact activation.2

example : targets.1.runMain 10 0 (words input) mem = .returned [33] mem := by cbv
example : Generic.Fuel.run model (inputEnv model input) 2 targets.2 =
    some (0, Generic.packResult model (out := word) (33 : Word)) := by cbv

example : targets.1.oracle 0 (words input) mem [33] mem :=
  (rtl_return_iff accepted _ _ _ _).mpr ⟨33, returns, rfl, rfl⟩

example : Eval (instruction model) (inputEnv model input) targets.2 mem 0
    (Generic.packResult model (out := word) (33 : Word)) mem :=
  (lambda_return_iff accepted _ _ _ _ _).mpr ⟨33, returns, rfl, rfl, rfl⟩

private theorem spinAbsent : source.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact source.not_returns_of_backedge_invariant model spin value (· = spin) (by cbv)
    (fun old fixed => by
      subst old
      exact ⟨spin, by cbv, rfl⟩)
    ((source.returns_iff_mem_denote model _ _).mpr present)

example :
    (∀ returned final, ¬ targets.1.oracle 0 (words spin) mem returned final) ∧
    (∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin)
      targets.2 mem label payload final) :=
  let iff := no_finite_return_iff accepted spin mem
  ⟨iff.1.mpr spinAbsent, iff.2.mpr spinAbsent⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native
