module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Pieces
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Identity
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Comparison

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.Whiskering

open ProgressiveGraph
open HorizontalPlacement (adjoin placed slots active_slot_label idle_slot_label active_slot_x idle_slot_x
  placedWires wire_data_active wire_data_idle LocatedWire)
open CollarAssociator (vertex_free_covers)

universe u v
variable {O : Type u} {S : Signature.{u,v} O}

theorem vertical_trace {W : ℕ} (d : ProgressiveGraph.Diagram S 0 W .point)
    (w : Fin W) (x : ℝ) (coord : ∀ y, d.x w y = x) :
    (d.wire w).trace = (fun y : ℝ => (x, y)) '' Set.Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨y, bounds, point⟩
    refine ⟨y, (vertex_free_covers d).mp bounds, ?_⟩
    change (d.x w y, y) = z at point
    rwa [coord] at point
  · rintro ⟨y, bounds, point⟩
    refine ⟨y, (vertex_free_covers d).mpr bounds, ?_⟩
    change (d.x w y, y) = z
    rwa [coord]

variable (s : ActiveStrip) (a idle : FixedCap S)

abbrev sourceId := placed s idle (a := a) (b := a) (FixedDrawing.identity S a.profile a.inside)

abbrev targetId := FixedDrawing.identity S (adjoin s a idle).profile (adjoin s a idle).inside

def identityWires : Fin (a.profile.size + idle.profile.size) ≃ Fin (adjoin s a idle).profile.size :=
  finSumFinEquiv.symm.trans (slots s a idle).symm

theorem identity_active (i : Fin a.profile.size) :
    identityWires s a idle (Fin.castAdd idle.profile.size i) = (slots s a idle).symm (.inl i) := by
  simp only [identityWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]

theorem identity_idle (i : Fin idle.profile.size) :
    identityWires s a idle (Fin.natAdd a.profile.size i) = (slots s a idle).symm (.inr i) := by
  simp only [identityWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]

theorem identity_labels (w : Fin (a.profile.size + idle.profile.size)) :
    (targetId s a idle).drawing.label (identityWires s a idle w) = (sourceId s a idle).drawing.label w := by
  change ((FixedDrawing.identitySpec (adjoin s a idle).profile (adjoin s a idle).inside).drawing S).label
      (identityWires s a idle w) =
    (placedWires s (FixedDrawing.identity S a.profile a.inside).drawing idle w).label
  rw [CollarSpec.drawing_label]
  change (adjoin s a idle).profile.label (identityWires s a idle w) =
    (placedWires s (FixedDrawing.identity S a.profile a.inside).drawing idle w).label
  induction w using Fin.addCases with
  | left i =>
    rw [identity_active, active_slot_label]
    exact (CollarSpec.drawing_label (S := S) (FixedDrawing.identitySpec a.profile a.inside) i).symm.trans
      (congrArg LocatedWire.label (wire_data_active s (FixedDrawing.identity S a.profile a.inside).drawing idle i)).symm
  | right i =>
    rw [identity_idle, idle_slot_label]
    exact (congrArg LocatedWire.label (wire_data_idle s (FixedDrawing.identity S a.profile a.inside).drawing idle i)).symm

theorem identity_coords (w : Fin (a.profile.size + idle.profile.size)) (y : ℝ) :
    (targetId s a idle).drawing.x (identityWires s a idle w) y = (sourceId s a idle).drawing.x w y := by
  refine (CapUnits.identity_x (S := S) (adjoin s a idle).inside (identityWires s a idle w) y).trans ?_
  change (adjoin s a idle).profile.x (identityWires s a idle w) =
    (placedWires s (FixedDrawing.identity S a.profile a.inside).drawing idle w).wire.x y
  induction w using Fin.addCases with
  | left i =>
    rw [identity_active, active_slot_x]
    exact (congrArg s.place (CapUnits.identity_x (S := S) a.inside i y).symm).trans
      (HorizontalPlacement.wire_x_active s (FixedDrawing.identity S a.profile a.inside).drawing idle i y).symm
  | right i =>
    rw [identity_idle, idle_slot_x]
    exact (HorizontalPlacement.wire_x_idle s (FixedDrawing.identity S a.profile a.inside).drawing idle i y).symm

def identityComparison : (sourceId s a idle).drawing.CapComparison (targetId s a idle).drawing where
  map := CapClasses.identity
  incidence :=
    { vertex := Equiv.refl _
      wire := identityWires s a idle
      generator i := i.elim0
      label := identity_labels s a idle
      inputs i := i.elim0
      outputs i := i.elim0 }
  trace w := by
    change id '' ((sourceId s a idle).drawing.wire w).trace = _
    rw [Set.image_id]
    let x := (adjoin s a idle).profile.x (identityWires s a idle w)
    have target := CapUnits.identity_x (S := S) (adjoin s a idle).inside (identityWires s a idle w)
    exact (vertical_trace _ w x (fun y => (identity_coords s a idle w y).symm.trans (target y))).trans
      (vertical_trace _ (identityWires s a idle w) x target).symm
  vertex i := i.elim0

end Silmaril.RuntimeWires.Proofs.Whiskering
