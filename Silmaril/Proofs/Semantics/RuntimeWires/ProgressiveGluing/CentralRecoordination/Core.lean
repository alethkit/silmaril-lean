module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CentralRecoordination.Knots
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Core

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CentralRecoordination

open ProgressiveGraph
open HorizontalPlacement (placed)
open MiddleAssociator (active_covers active_data idle_data CoreTransport)
open HorizontalComparison (drawing_inputs drawing_outputs)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a a' b d : FixedCap S}
variable (side : ActiveStrip) (h : a.types = a'.types) (p : FixedDrawing S b.profile d.profile)

local notation "L" => placed side a p
local notation "R" => placed side a' p

def wires : Fin (p.wires + a.profile.size) ≃ Fin (p.wires + a'.profile.size) :=
  finSumFinEquiv.symm.trans
    (((Equiv.refl _).sumCongr (FixedCap.recoordinationSlots h).toEquiv).trans finSumFinEquiv)

theorem wires_active (w : Fin p.wires) :
    wires h p (Fin.castAdd a.profile.size w) = Fin.castAdd a'.profile.size w := by
  simp only [wires, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply, finSumFinEquiv_apply_left]

theorem wires_idle (i : Fin a.profile.size) :
    wires h p (Fin.natAdd p.wires i) = Fin.natAdd p.wires (FixedCap.recoordinationSlots h i) := by
  simp only [wires, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]
  rfl

theorem label (w : Fin (L).wires) :
    (R).drawing.label (wires h p w) = (L).drawing.label w := by
  induction w using Fin.addCases with
  | left w =>
    rw [wires_active]
    exact (congrArg Prod.fst (active_data side p.drawing a' w 0)).trans
      (congrArg Prod.fst (active_data side p.drawing a w 0)).symm
  | right i =>
    rw [wires_idle]
    exact (congrArg Prod.fst (idle_data side p.drawing a' (FixedCap.recoordinationSlots h i) 0)).trans
      ((FixedCap.recoordination_label h i).symm.trans (congrArg Prod.fst (idle_data side p.drawing a i 0)).symm)

theorem coordinate (w : Fin (L).wires) (y : ℝ) (hw : (L).drawing.covers w y) :
    (R).drawing.x (wires h p w) y = horizontal side h ((L).drawing.x w y) := by
  induction w using Fin.addCases with
  | left w =>
    rw [wires_active]
    have covered := (active_covers side p.drawing a w y).mp hw
    have inside : p.drawing.x w y ∈ Set.Ioo (0 : ℝ) 1 := p.drawing.wire_inside w y covered
    exact (congrArg Prod.snd (active_data side p.drawing a' w y)).trans
      ((horizontal_active side h inside).symm.trans
        (congrArg (horizontal side h) (congrArg Prod.snd (active_data side p.drawing a w y)).symm))
  | right i =>
    rw [wires_idle]
    exact (congrArg Prod.snd (idle_data side p.drawing a' (FixedCap.recoordinationSlots h i) y)).trans
      ((horizontal_idle side h i).symm.trans
        (congrArg (horizontal side h) (congrArg Prod.snd (idle_data side p.drawing a i y)).symm))

theorem port_map (xs : List (Fin p.wires)) :
    (xs.map (Fin.castAdd a.profile.size)).map (wires h p) = xs.map (Fin.castAdd a'.profile.size) :=
  (List.map_map ..).trans (congrArg (fun f => xs.map f) (funext (wires_active h p)))

def incidence : (L).drawing.IncidenceEquiv (R).drawing where
  vertex := Equiv.refl _
  wire := wires h p
  generator _ := rfl
  label := label side h p
  inputs j := (drawing_inputs side a' p.drawing j).trans
    ((congrArg (List.map (wires h p)) (drawing_inputs side a p.drawing j)).trans
      (port_map h p _)).symm
  outputs j := (drawing_outputs side a' p.drawing j).trans
    ((congrArg (List.map (wires h p)) (drawing_outputs side a p.drawing j)).trans
      (port_map h p _)).symm

/-- The core transport keeps every vertex and active trace fixed in the
selected strip, and relabels the other strip by its ordered idle slots. -/
def core : CoreTransport (horizontal side h) (L) (R) where
  incidence := incidence side h p
  vertex_x j := (horizontal_active side h (p.drawing.vertex_inside j).1).symm
  vertex_height _ := rfl
  wire_x := coordinate side h p

end Silmaril.RuntimeWires.Proofs.CentralRecoordination
