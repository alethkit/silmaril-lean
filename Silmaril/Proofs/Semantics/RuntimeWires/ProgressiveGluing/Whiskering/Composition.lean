module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Traces
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Vertices
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Comparison

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.Whiskering

open ProgressiveGraph CollarAssociator
open CapClasses (matching glue)
open HorizontalPlacement (drawing placedWires wire_data_active wire_data_idle)
open HorizontalComparison (drawing_inputs drawing_outputs)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c : FixedCap S}
variable (s : ActiveStrip) (idle : FixedCap S)
variable (p : FixedDrawing S a.profile b.profile) (q : FixedDrawing S b.profile c.profile)

local notation "I" => idle.profile.size
local notation "m" => matching p q
local notation "n" => wideMatch s idle p q
local notation "P" => stackThenPlace s idle p q
local notation "Q" => placeThenStack s idle p q
local notation "ren" => wireEquiv s idle p q

theorem comp_generator (j : Fin (p.vertices + q.vertices)) :
    (Q).drawing.generator j = (P).drawing.generator j := by
  change (n).glue.generator j = (m).glue.generator j
  induction j using Fin.addCases with
  | left v => exact (generator_lower n v).trans (generator_lower m v).symm
  | right v => exact (generator_upper n v).trans (generator_upper m v).symm

theorem comp_label (w : Fin ((glue p q).wires + I)) :
    (Q).drawing.label (ren w) = (P).drawing.label w := by
  change (n).glue.label (forward s idle p q w) = (placedWires s (m).glue idle w).label
  induction w using Fin.addCases with
  | left w =>
    rcases wire_cases m w with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [forward_active_lower]
      exact (left_label n _).trans <|
        (congrArg HorizontalPlacement.LocatedWire.label
          (wire_data_active s p.drawing idle i)).trans <|
        ((congrArg HorizontalPlacement.LocatedWire.label
          (wire_data_active s (m).glue idle (leftWire m i))).trans (left_label m i)).symm
    · rw [forward_active_upper]
      exact (right_label n _).trans <|
        (congrArg HorizontalPlacement.LocatedWire.label
          (wire_data_active s q.drawing idle i)).trans <|
        ((congrArg HorizontalPlacement.LocatedWire.label
          (wire_data_active s (m).glue idle (rightWire m i))).trans (right_label m i)).symm
  | right i =>
    rw [forward_idle_lower]
    exact (left_label n _).trans <|
      (congrArg HorizontalPlacement.LocatedWire.label
        (wire_data_idle s p.drawing idle i)).trans <|
      (congrArg HorizontalPlacement.LocatedWire.label (wire_data_idle s (m).glue idle i)).symm

theorem port_names_lower (xs : List (Fin p.wires)) :
    (xs.map (Fin.castAdd I)).map (leftWire n) =
      ((xs.map (leftWire m)).map (Fin.castAdd I)).map ren := by
  exact (List.map_map ..).trans <|
    (congrArg (fun f => xs.map f) (funext fun i => (forward_active_lower s idle p q i).symm)).trans <|
    ((List.map_map ..).trans (List.map_map ..)).symm

theorem port_names_upper (xs : List (Fin q.wires)) :
    (xs.map (Fin.castAdd I)).map (rightWire n) =
      ((xs.map (rightWire m)).map (Fin.castAdd I)).map ren := by
  exact (List.map_map ..).trans <|
    (congrArg (fun f => xs.map f) (funext fun i => (forward_active_upper s idle p q i).symm)).trans <|
    ((List.map_map ..).trans (List.map_map ..)).symm

theorem comp_inputs (j : Fin (p.vertices + q.vertices)) :
    (Q).drawing.inputs j = ((P).drawing.inputs j).map ren := by
  change (n).glue.inputs j = ((drawing s (m).glue idle).inputs j).map ren
  rw [drawing_inputs]
  induction j using Fin.addCases with
  | left v =>
    rw [inputs_lower m v]
    exact (inputs_lower n v).trans <|
      (congrArg (List.map (leftWire n)) (drawing_inputs s idle p.drawing v)).trans <|
      port_names_lower s idle p q _
  | right v =>
    rw [inputs_upper m v]
    exact (inputs_upper n v).trans <|
      (congrArg (List.map (rightWire n)) (drawing_inputs s idle q.drawing v)).trans <|
      port_names_upper s idle p q _

theorem comp_outputs (j : Fin (p.vertices + q.vertices)) :
    (Q).drawing.outputs j = ((P).drawing.outputs j).map ren := by
  change (n).glue.outputs j = ((drawing s (m).glue idle).outputs j).map ren
  rw [drawing_outputs]
  induction j using Fin.addCases with
  | left v =>
    rw [outputs_lower m v]
    exact (outputs_lower n v).trans <|
      (congrArg (List.map (leftWire n)) (drawing_outputs s idle p.drawing v)).trans <|
      port_names_lower s idle p q _
  | right v =>
    rw [outputs_upper m v]
    exact (outputs_upper n v).trans <|
      (congrArg (List.map (rightWire n)) (drawing_outputs s idle q.drawing v)).trans <|
      port_names_upper s idle p q _

theorem comp_vertex (j : Fin (p.vertices + q.vertices)) :
    ((P).drawing.vertexX j, (P).drawing.vertexHeight j) =
      ((Q).drawing.vertexX j, (Q).drawing.vertexHeight j) := by
  change (s.place ((m).glue.vertexX j), (m).glue.vertexHeight j) =
    ((n).glue.vertexX j, (n).glue.vertexHeight j)
  induction j using Fin.addCases with
  | left v =>
    exact Prod.ext ((congrArg s.place (vertexX_lower m v)).trans (vertexX_lower n v).symm)
      ((height_lower m v).trans (height_lower n v).symm)
  | right v =>
    exact Prod.ext ((congrArg s.place (vertexX_upper m v)).trans (vertexX_upper n v).symm)
      ((height_upper m v).trans (height_upper n v).symm)

def compositionComparison : (P).drawing.CapComparison (Q).drawing where
  map := CapClasses.identity
  incidence :=
    { vertex := Equiv.refl _
      wire := ren
      generator := comp_generator s idle p q
      label := comp_label s idle p q
      inputs := comp_inputs s idle p q
      outputs := comp_outputs s idle p q }
  trace w := by
    change id '' ((P).drawing.wire w).trace = ((Q).drawing.wire (ren w)).trace
    rw [Set.image_id]
    ext z
    exact (stack_place_trace s idle p q w z).trans (place_stack_trace s idle p q w z).symm
  vertex := comp_vertex s idle p q

end Silmaril.RuntimeWires.Proofs.Whiskering
