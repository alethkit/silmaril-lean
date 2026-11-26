module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair

open Silmaril.SSA
open SeaOfNodes.Diamond
open SeaOfNodes.Diamond.AddPhi (Result scanLiterals scanLiterals_agrees literalArm_eval)
open SeaOfNodes.Diamond.AddPhi.Pair
open SeaOfNodes.Pure.ConstantFold
open SeaOfNodes.Pure.SubZero (model word wordPort)
open RVSDG (Locals Tuple extend)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : Source inputs sigs} {target : Result inputs sigs}

theorem accepted_eq (accepted : rewrite? g = some target) :
    let known : Literals (dataPorts inputs) (extend [] sigs) := scanLiterals (fun _ => none) g.shared
    ∃ first second, armLiterals? known (g.arms .first) = some first ∧
      armLiterals? known (g.arms .second) = some second ∧
      eligible first second = true ∧ target = emit g first second := by
  unfold rewrite? at accepted
  obtain ⟨first, firstEq, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨second, secondEq, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i admitted
    exact ⟨first, second, firstEq, secondEq, admitted, (Option.some.inj accepted).symm⟩
  · contradiction

private theorem armLiterals_eval {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    {known : Literals args past} {arm : Arms.Arm SeaOfNodes.Pure.SubZero.Opcode args past [word, word]}
    {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
    (agree : Scan.Literals.Agrees known entry locals) {operands : Operands}
    (found : armLiterals? known arm = some operands) : arm.eval model entry locals = operands :=
  Scan.literalInputs_sound (scanLiterals_agrees arm.dataflow known entry locals agree) arm.outputs found

theorem keeps_control (accepted : rewrite? g = some target) :
    target.shared = g.shared ∧ target.predicate = g.predicate ∧ target.merge = g.merge := by
  obtain ⟨first, second, _, _, _, rfl⟩ := accepted_eq accepted
  exact ⟨rfl, rfl, rfl⟩

theorem slot_eval_eq (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (target.arms slot).eval model entry (target.shared.eval model entry PUnit.unit) =
      .cons (sourceAt g entry slot) .nil := by
  obtain ⟨first, second, firstEq, secondEq, _, rfl⟩ := accepted_eq accepted
  have facts : Scan.Literals.Agrees (scanLiterals (fun _ => none) g.shared) entry
      (g.shared.eval model entry PUnit.unit) :=
    scanLiterals_agrees g.shared (fun _ => none) entry PUnit.unit (by intro _ _ _ h; contradiction)
  cases slot
  · simpa only [emit, sourceAt, armLiterals_eval facts firstEq] using
      literalArm_eval entry (g.shared.eval model entry PUnit.unit) (add first)
  · simpa only [emit, sourceAt, armLiterals_eval facts secondEq] using
      literalArm_eval entry (g.shared.eval model entry PUnit.unit) (add second)

theorem denote_eq (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    target.denote model entry = .cons (sourceDenote g entry) .nil := by
  obtain ⟨sharedEq, predicateEq, mergeEq⟩ := keeps_control accepted
  unfold Arms.Graph.denote sourceDenote
  rw [slot_eval_eq accepted, sharedEq, predicateEq, mergeEq]
  rfl

theorem returns_iff (accepted : rewrite? g = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (result : BitVec 64) :
    target.Returns model entry (.cons result .nil) ↔ SourceReturns g entry result := by
  rw [Arms.Graph.returns_iff_denote, denote_eq accepted]
  simp only [SourceReturns, Arms.Graph.returns_iff_denote]
  constructor
  · intro equal
    exact ⟨g.denote model entry, rfl, congrArg (fun row => row.get .head) equal⟩
  · rintro ⟨_, rfl, equal⟩
    exact congrArg (fun v : BitVec 64 => Tuple.cons (F := Val model.value) (t := wordPort) v .nil) equal

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair
