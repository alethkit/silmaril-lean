module

public import Silmaril.SSA.SeaOfNodes.GCM.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} (tree : DominatorTree cfg)

private theorem valid_of_check {point : Point Label} (checked : point.valid? tree = true) :
    point.Valid cfg := by
  simp only [Point.valid?, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨tree.reachable_sound checked.1, checked.2⟩

private theorem available_of_check {defSite read : Point Label}
    (reachable : Reachable cfg read.block) (checked : defSite.available? tree read = true) :
    defSite.AvailableAt cfg read := by
  simp only [Point.available?, Bool.and_eq_true, List.isPrefixOf_iff_prefix,
    decide_eq_true_eq] at checked
  exact ⟨tree.prefix_sound reachable checked.1, fun same => checked.2 (congrArg tree.address same)⟩

theorem phi_point?_eq_some_iff (source : BlockId Label) (slot : EdgeSlot) (argument : Nat)
    (point : Point Label) :
    (Use.phi source slot argument).point? cfg = some point ↔
      (∃ dst, (shape cfg source).target slot = some dst ∧ argument < dst.1.length) ∧
      point = ⟨source, (shape cfg source).bindings⟩ := by
  cases edge : (shape cfg source).target slot with
  | none => simp [Use.point?, edge]
  | some dst =>
    by_cases inRange : argument < dst.1.length <;>
      simp [Use.point?, edge, inRange, eq_comm]

theorem checkPlacement_sound {operands : List (Point Label)} {uses : List (Use Label)}
    {candidate : Point Label} (checked : checkPlacement tree operands uses candidate = true) :
    Legal cfg operands uses candidate := by
  simp only [checkPlacement, checkPlacementWith, Bool.and_eq_true, List.all_eq_true] at checked
  have candidateValid := valid_of_check tree checked.1.1
  refine ⟨candidateValid, ?_, ?_⟩
  · intro operand member
    have checks := checked.1.2 operand member
    exact ⟨valid_of_check tree checks.1, available_of_check tree candidateValid.1 checks.2⟩
  · intro use member
    have checks := checked.2 use member
    cases resolved : use.point? cfg with
    | none => simp [resolved] at checks
    | some point =>
      simp only [resolved, Option.any_some, Bool.and_eq_true] at checks
      have pointValid := valid_of_check tree checks.1
      exact ⟨point, rfl, pointValid, available_of_check tree pointValid.1 checks.2⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM
