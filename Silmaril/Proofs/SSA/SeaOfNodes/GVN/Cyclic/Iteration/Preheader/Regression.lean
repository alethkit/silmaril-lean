module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Regression

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty ValueSort dataPorts)
open GVN.Cyclic.Activation (Inputs headerInput headerLatch inputSlot)
open GVN.Cyclic.Builder.Preheader (Native)
open GVN.Cyclic.Deletion (DeletedLoop)
open GVN.Cyclic.Iteration.Preheader
open Pure.SubZero (Opcode model word wordPort)
open Silmaril.SSA.RVSDG (Port Wires extend)
open scoped Pure.WordNormalize

private abbrev inputs : List (ValueSort Unit) := [.predicate, .predicate, word, word]
private abbrev carried : List (ValueSort Unit) := [.predicate, word, word, word]
private abbrev entrySigs : List (List (Ty Unit)) := [[wordPort], [wordPort], [wordPort]]
private abbrev headerSigs : List (List (Ty Unit)) := [[wordPort], [wordPort], [wordPort], [wordPort], [wordPort]]

private def y : Port inputs word := .tail (.tail .head)
private def z : Port inputs word := .tail (.tail (.tail .head))
private def firstLane : Port carried word := .tail .head
private def secondLane : Port carried word := .tail (.tail .head)
private def thirdLane : Port carried word := .tail (.tail (.tail .head))

private def increment {past : List (List (Ty Unit))} (lane : Port carried word) :
    Wires (Loop.headerPorts inputs carried) past [wordPort, wordPort] :=
  .cons (.arg (headerLatch (inputSlot lane) (dataPorts inputs)))
    (.cons (.arg (headerInput (dataPorts carried) y)) .nil)

private def seedOperands {past : List (List (Ty Unit))} :
    Wires (dataPorts inputs) past [wordPort, wordPort] :=
  .cons (.arg (inputSlot y)) (.cons (.arg (inputSlot z)) .nil)

private def feedback {sigs : List (List (Ty Unit))} (same : Bool)
    (last : Fin (extend [] sigs).length) (port : Port (extend [] sigs)[last] wordPort) :
    Wires (Loop.headerPorts inputs carried) (extend [] sigs) (dataPorts carried) :=
  .cons (.arg (headerInput (dataPorts carried) (.tail .head)))
    (.cons (.output last port)
      (.cons (if same then .output last port else .arg (headerInput (dataPorts carried) y))
        (.cons (if same then .output last port else .arg (headerInput (dataPorts carried) z)) .nil)))

private def fixture (sameFeedback : Bool) : Native inputs carried entrySigs headerSigs word where
  preheader := .cons .add seedOperands (.cons .add seedOperands (.cons .add seedOperands .nil))
  header := .cons .add (increment firstLane)
    (.cons .add (increment secondLane)
      (.cons .add (increment thirdLane)
        (.cons .add (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
          (.cons .add (.cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil)) .nil))))
  phiInputs
    | .entry =>
      .cons (.arg .head) (.cons (.output (0 : Fin 3) .head)
        (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil)))
    | .backedge => feedback (sigs := headerSigs) sameFeedback (4 : Fin 5) .head
  predicate := .arg (headerLatch (.head : Port (dataPorts carried) (.value .predicate)) (dataPorts inputs))
  result := .output (4 : Fin 5) .head

private def afterFirst : DeletedLoop Opcode inputs carried entrySigs word :=
  ⟨[[wordPort], [wordPort], [wordPort], [wordPort]], {
    preheader := (fixture true).preheader
    header := .cons .add (increment secondLane)
      (.cons .add (increment thirdLane)
        (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil))
          (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil)))
    phiInputs
      | .entry => (fixture true).phiInputs .entry
      | .backedge => feedback (sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]) true (3 : Fin 4) .head
    predicate := .arg (headerLatch (.head : Port (dataPorts carried) (.value .predicate)) (dataPorts inputs))
    result := .output (3 : Fin 4) .head }⟩

private def afterSecond : DeletedLoop Opcode inputs carried entrySigs word :=
  ⟨[[wordPort], [wordPort], [wordPort]], {
    preheader := (fixture true).preheader
    header := .cons .add (increment secondLane)
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil))
        (.cons .add (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)) .nil))
    phiInputs
      | .entry => (fixture true).phiInputs .entry
      | .backedge => feedback (sigs := [[wordPort], [wordPort], [wordPort]]) true (2 : Fin 3) .head
    predicate := .arg (headerLatch (.head : Port (dataPorts carried) (.value .predicate)) (dataPorts inputs))
    result := .output (2 : Fin 3) .head }⟩

private theorem first_accepted :
    GVN.Cyclic.Builder.Preheader.optimize? (fixture true) = some afterFirst := rfl

private theorem second_accepted :
    GVN.Cyclic.Builder.Preheader.optimize? afterFirst.graph = some afterSecond := rfl

private theorem final_step : GVN.Cyclic.Builder.Preheader.optimize? afterSecond.graph = none := rfl

private theorem run_result : normalize (fixture true) = ⟨afterSecond, 2⟩ := by
  change run 5 (fixture true) = _
  rw [run_succ 4 (fixture true), first_accepted]
  dsimp only
  rw [run_succ 3 afterFirst.graph, second_accepted]
  dsimp only
  rw [run_succ 2 afterSecond.graph, final_step]

theorem two_restored_native_steps :
    (run 1 (fixture true)).rewrite = afterFirst ∧
      (normalize (fixture true)).rewrite.headerSigs.length = 3 ∧ (normalize (fixture true)).deletions = 2 := by
  rw [run_result]
  refine ⟨?_, rfl, rfl⟩
  rw [run_succ 0 (fixture true), first_accepted]
  rfl

private def input : Inputs model inputs :=
  .cons ⟨true⟩ (.cons ⟨false⟩ (.cons (3 : BitVec 64) (.cons (4 : BitVec 64) .nil)))

theorem native_observations_survive_both_rewrites :
    let final := (normalize (fixture true)).rewrite.graph
    final.step model input (final.initial model input) =
      .inr (.cons ⟨false⟩ (.cons (30 : BitVec 64) (.cons (30 : BitVec 64) (.cons (30 : BitVec 64) .nil)))) ∧
    final.evalBackedges model 0 input = none ∧ final.evalBackedges model 1 input = some (99 : BitVec 64) ∧
    (final.Returns model input (99 : BitVec 64) ↔ (fixture true).Returns model input (99 : BitVec 64)) := by
  refine ⟨?_, (normalize_evalBackedges (fixture true) input 0).trans rfl,
    (normalize_evalBackedges (fixture true) input 1).trans rfl,
    normalize_returns (fixture true) input (99 : BitVec 64)⟩
  rw [run_result]
  rfl

private theorem mismatched_feedback_step :
    GVN.Cyclic.Builder.Preheader.optimize? (fixture false) = none := rfl

theorem mismatched_feedback_is_an_admitted_fixed_point :
    (GVN.Cyclic.Builder.build? (GVN.Cyclic.Builder.Preheader.prepare (fixture false))).isSome = true ∧
      normalize (fixture false) = ⟨⟨headerSigs, fixture false⟩, 0⟩ := by
  refine ⟨rfl, ?_⟩
  change run 5 (fixture false) = _
  rw [run_succ 4 (fixture false), mismatched_feedback_step]

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Regression
