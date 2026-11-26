module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Phi.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Phi

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Prog run_returned)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom encode encodeTuple inputEnv instruction terminatorRegion)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def specs : List FeedbackSpec := [⟨.sub, 0, 1, 2⟩, ⟨.add, 1, 0, 1⟩]
private def plan : FeedbackPlan 3 where
  routes :=
    ⟨.cons (.arg (argumentPort 4 1))
        (.cons (.arg (argumentPort 4 2)) (.cons (.arg (argumentPort 4 3)) .nil)),
      .cons (.arg (argumentPort 8 5))
        (.cons (.arg (argumentPort 8 6)) (.cons (.arg (argumentPort 8 5)) .nil)),
      1⟩
  updates := [⟨.sub, 0, 1, 2⟩, ⟨.add, 1, 0, 1⟩]

private theorem accepted : checkFeedbackPlan 3 [1, 2, 3] [5, 6, 5] 1 specs = some plan := by cbv

example : lowerFeedbackRowChecked 3 [1, 2, 3] [5, 6, 5] 1 specs = some plan.rtl :=
  plan.checked_rtl accepted

example : plan.ssa.HasType (inputContext (wordSorts 4)) [packed [.value word]] := plan.ssa_hasType

private def memory : Memory := Memory.ofList 4 [49, 27, 13, 54]
private def old : WordTuple 4 := pack 1 10 20 30
private def next : WordTuple 4 := pack 0 (-10) 30 10

private def feedbackFirst : Fin 2 ≃ Incoming where
  toFun := Fin.cases .backedge (fun _ => .entry)
  invFun := Incoming.select 1 0
  left_inv := fun i => Fin.cases rfl (fun j => by rw [Fin.fin_one_eq_zero j]; rfl) i
  right_inv := fun arrival => by cases arrival <;> rfl

private def order : Fin 2 ≃ HeaderIncoming plan.graph :=
  feedbackFirst.trans (headerIncomingEquiv plan.graph)

example : slotBranch plan.graph order 0 = .br 0 (edge plan.graph .backedge).argument :=
  slot_branch_roundtrip plan.graph order (headerIncoming plan.graph .backedge)

example : slotBranch plan.graph order 1 = .br 0 (edge plan.graph .entry).argument :=
  slot_branch_roundtrip plan.graph order (headerIncoming plan.graph .entry)

-- Values in binder order for the six scheduled producers, then the case unit.
private def selectedEnv : Env (Atom model) :=
  let env := unpackEnv model old (inputEnv model old)
  let one := extend env (encode model (sort := word) (1 : Word))
  let dec := extend one (encode model (sort := word) (0 : Word))
  let zero := extend dec (encode model (sort := word) (0 : Word))
  let guard := extend zero (.inl .unit)
  let subtract := extend guard (encode model (sort := word) (-10 : Word))
  let add := extend subtract (encode model (sort := word) (30 : Word))
  extend add .unit

example : Eval (instruction model) selectedEnv
    (terminatorRegion (slotBranch plan.graph order 0)) memory 0 (encodeTuple model next) memory :=
  (slot_transfer_iff plan.graph model order 0 selectedEnv memory memory 0 _).mpr ⟨rfl, rfl, rfl⟩

private abbrev HeaderTransfers (latched : WordTuple 4) :=
  Eval (instruction model) (extend (inputEnv model old) (encodeTuple model old))
    (header plan.graph) memory 0 (encodeTuple model latched) memory

example : HeaderTransfers next :=
  (header_backedge_iff plan.graph model old old next memory memory).mpr ⟨by cbv, rfl⟩

-- A sequential clobber would read the new first payload for add and copy.
example : ¬ HeaderTransfers (pack 0 (-10) 10 (-10)) := by
  intro run
  have native := ((header_backedge_iff plan.graph model old old _ memory memory).mp run).1
  have mismatch : Sum.inr next = Sum.inr (pack 0 (-10) 10 (-10)) := native
  cases mismatch

private theorem ssa_of_run (input : WordTuple 4) (fuel : Nat) (value : Word)
    (run : plan.rtl.runMain fuel 0 (words input) memory = .returned [value] memory) :
    Eval (instruction model) (inputEnv model input) plan.ssa
      memory 0 (packResult model (out := word) value) memory := by
  have rtl : plan.rtl.oracle 0 (words input) memory [value] memory := by
    unfold Prog.runMain at run
    split at run
    · exact ⟨_, by assumption, run_returned run⟩
    · cases run
  obtain ⟨observed, same, eval⟩ := (plan.returns_iff input memory memory [value]).mp rtl
  cases same
  exact eval

example : Eval (instruction model) (inputEnv model old) plan.ssa
    memory 0 (packResult model (out := word) (30 : Word)) memory :=
  ssa_of_run old 16 30 (by cbv)

example : Eval (instruction model) (inputEnv model (pack 0 10 20 30)) plan.ssa
    memory 0 (packResult model (out := word) (20 : Word)) memory :=
  ssa_of_run (pack 0 10 20 30) 9 20 (by cbv)

example : checkFeedbackPlan 3 [1, 2, 3] [5, 6, 5] 1
    [⟨.sub, 0, 1, 2⟩, ⟨.add, 0, 0, 1⟩] = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Phi
