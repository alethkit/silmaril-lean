module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering

open CategoryTheory
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.LambdaSSA (packet)
open RVSDG (Port)

private def sig : EntrySignature := ⟨[.address, .address, .word, .word]⟩

private def swap : sig ⟶ sig :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail .head) => .tail (.tail .head)
    | .tail (.tail (.tail .head)) => .tail (.tail (.tail .head))⟩

private def loop (dest : Port sig.args .address) : Graph sig.args :=
  let writeWord : Port sig.args .word := .tail (.tail (.tail .head))
  ⟨.load (.latest 0) (.arg .head)
      (.store (.latest 0) (.arg dest) (.arg writeWord)
        (.ret (.latest 1) (.output (0 : Fin 1) .head))),
    rfl, .tail (.tail .head)⟩

private def equation : Equation sig :=
  ⟨loop (.tail .head), loop .head⟩

private def firstCell : Address 2 := 0
private def secondCell : Address 2 := 1

private def model : EntryModel sig :=
  ⟨2, .cons firstCell (.cons secondCell (.cons (0 : Word) (.cons (17 : Word) .nil)))⟩

private def initial : Heap model.cells := fun _ => 0
private def leftHeap : Heap model.cells := initial.write secondCell 17
private def rightHeap : Heap model.cells := initial.write firstCell 17

private theorem member (graph : Graph sig.args) (final : Heap model.cells)
    (run : graph.evalAfter model.input initial 0 = some (0, final)) :
    (0, final) ∈ graph.denote model.input initial :=
  (graph.returns_iff_mem_denote model.input initial 0 final).1
    ⟨0, (graph.returnsAfter_iff_evalAfter model.input initial 0 0 final).2 run⟩

-- Each loop loads zero, stores 17 and exits. The store destinations differ.
example : lambdaReturns (lowerLambda equation.lhs) model initial 0 (packet 0) leftHeap :=
  (lambda_observation_iff equation.lhs model initial leftHeap 0 (packet 0)).2
    ⟨0, member _ _ (by cbv), rfl, rfl⟩

example : lambdaReturns (lowerLambda equation.rhs) model initial 0 (packet 0) rightHeap :=
  (lambda_observation_iff equation.rhs model initial rightHeap 0 (packet 0)).2
    ⟨0, member _ _ (by cbv), rfl, rfl⟩

example : thetaObservation equation.lhs model initial = Part.some (encodeResult 0 leftHeap) :=
  (theta_observation_iff equation.lhs model initial 0 leftHeap).2 (member _ _ (by cbv))

example : thetaObservation equation.rhs model initial = Part.some (encodeResult 0 rightHeap) :=
  (theta_observation_iff equation.rhs model initial 0 rightHeap).2 (member _ _ (by cbv))

-- The nonidentity map moves the left loop's store to cell zero.
example :
    thetaObservation (equation.map swap).lhs model initial = Part.some (encodeResult 0 rightHeap) :=
  (theta_observation_iff _ model initial 0 rightHeap).2 (member _ _ (by cbv))

private theorem different : ¬ (equation.map swap).Holds model := by
  intro holds
  have lhs := member (equation.map swap).lhs rightHeap (by cbv)
  have rhs := member (equation.map swap).rhs leftHeap (by cbv)
  have same := Part.mem_unique ((holds initial) ▸ lhs) rhs
  have atCell := congrArg (fun (result : Word × Heap model.cells) => result.2 firstCell) same
  have right : rightHeap firstCell = 17 := by cbv
  have left : leftHeap firstCell = 0 := by cbv
  exact (by decide : (17 : Word) ≠ 0) (right.symm.trans (atCell.trans left))

example : ¬ lambdaHolds (equation.map swap) model :=
  fun holds => different ((lambda_satisfaction _ model).1 holds)

example : ¬ thetaHolds equation (reduct swap model) :=
  fun holds => different ((theta_satisfaction _ model).1
    ((theta_satisfaction_reindex swap equation model).2 holds))

private def cycling : Heap 2 := fun address => if address = firstCell then 1 else 17

private theorem fixed : equation.lhs.step model.input cycling = .inr cycling := by
  have same : cycling.write secondCell 17 = cycling :=
    Function.update_eq_self_iff.2 (by cbv)
  change (if (1 : Word) = 0 then Sum.inl (1, cycling.write secondCell 17)
    else Sum.inr (cycling.write secondCell 17)) = .inr cycling
  rw [ite_eq_right (by decide : (1 : Word) ≠ 0), same]

private theorem noNativeReturn : equation.lhs.denote model.input cycling = Part.none := by
  apply Part.eq_none_iff.2
  rintro ⟨word, final⟩ observed
  have source := (equation.lhs.returns_iff_mem_denote model.input cycling word final).2 observed
  obtain ⟨fuel, run⟩ := (equation.lhs.lowerTheta_returns_iff model.input cycling word final).1 source
  rw [equation.lhs.lowerTheta_run_none_of_fixed_backedge model.input cycling fixed fuel] at run
  cases run

example : ∀ label payload final,
    ¬ lambdaReturns (lowerLambda equation.lhs) model cycling label payload final :=
  (lambda_no_return_iff equation.lhs model cycling).2 noNativeReturn

example : thetaObservation equation.lhs model cycling = Part.none :=
  (theta_no_return_iff equation.lhs model cycling).2 noNativeReturn

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering
