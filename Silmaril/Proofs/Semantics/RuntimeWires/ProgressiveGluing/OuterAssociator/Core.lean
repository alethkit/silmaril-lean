module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.MiddleAssociator.Core
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OuterAssociator.Defs

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.OuterAssociator

open ProgressiveGraph
open HorizontalPlacement (adjoin placed slots active_slot_label idle_slot_label active_slot_x idle_slot_x)
open HorizontalComparison (drawing_inputs drawing_outputs)
open MiddleAssociator (CoreTransport active_covers active_data idle_data horizontal
  horizontal_left horizontal_middle horizontal_right leftKnots rightKnots left_strict right_strict)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : FixedCap S}
variable (side : ActiveStrip) (near far : FixedCap S) (p : FixedDrawing S a.profile b.profile)

abbrev inner := placed side near p
abbrev nested := placed side far (a := adjoin side a near) (b := adjoin side b near) (inner side near p)
abbrev grouped := placed side (adjoin side near far) p

abbrev WireNames := Fin p.wires ⊕ (Fin near.profile.size ⊕ Fin far.profile.size)

/-- Both drawings use the original active wire IDs and the two idle
slot IDs. In the grouped drawing the idle IDs use the order of the
combined idle profile. -/
def nestedNames : WireNames near far p ≃ Fin (nested side near far p).wires :=
  (Equiv.sumAssoc _ _ _).symm.trans
    ((finSumFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv)

def groupedNames : WireNames near far p ≃ Fin (grouped side near far p).wires :=
  ((Equiv.refl _).sumCongr (slots side near far).symm).trans finSumFinEquiv

def renameWires : Fin (nested side near far p).wires ≃ Fin (grouped side near far p).wires :=
  (nestedNames side near far p).symm.trans (groupedNames side near far p)

theorem rename_at (w : WireNames near far p) :
    renameWires side near far p (nestedNames side near far p w) = groupedNames side near far p w := by
  simp only [renameWires, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem nested_active (w : Fin p.wires) :
    nestedNames side near far p (.inl w) = Fin.castAdd far.profile.size (Fin.castAdd near.profile.size w) := rfl

theorem grouped_active (w : Fin p.wires) :
    groupedNames side near far p (.inl w) = Fin.castAdd (adjoin side near far).profile.size w := rfl

def wireLabel : WireNames near far p → O
  | .inl w => p.drawing.label w
  | .inr (.inl i) => near.profile.label i
  | .inr (.inr i) => far.profile.label i

theorem nested_data (w : WireNames near far p) (y : ℝ) :
    ((nested side near far p).drawing.label (nestedNames side near far p w),
        (nested side near far p).drawing.x (nestedNames side near far p w) y) =
      (wireLabel near far p w, match w with
        | .inl i => side.place (side.place (p.drawing.x i y))
        | .inr (.inl i) => side.place (side.opposite.place (near.profile.x i))
        | .inr (.inr i) => side.opposite.place (far.profile.x i)) := by
  rcases w with i | (i | i)
  · exact (active_data side (inner side near p).drawing far _ y).trans
      (congrArg (fun z => (z.1, side.place z.2)) (active_data side p.drawing near i y))
  · exact (active_data side (inner side near p).drawing far _ y).trans
      (congrArg (fun z => (z.1, side.place z.2)) (idle_data side p.drawing near i y))
  · exact idle_data side (inner side near p).drawing far i y

theorem grouped_data (w : WireNames near far p) (y : ℝ) :
    ((grouped side near far p).drawing.label (groupedNames side near far p w),
        (grouped side near far p).drawing.x (groupedNames side near far p w) y) =
      (wireLabel near far p w, match w with
        | .inl i => side.place (p.drawing.x i y)
        | .inr (.inl i) => side.opposite.place (side.place (near.profile.x i))
        | .inr (.inr i) => side.opposite.place (side.opposite.place (far.profile.x i))) := by
  rcases w with i | (i | i)
  · exact active_data side p.drawing (adjoin side near far) i y
  · exact (idle_data side p.drawing (adjoin side near far) ((slots side near far).symm (.inl i)) y).trans
      (Prod.ext (active_slot_label side near far i)
        (congrArg side.opposite.place (active_slot_x side near far i)))
  · exact (idle_data side p.drawing (adjoin side near far) ((slots side near far).symm (.inr i)) y).trans
      (Prod.ext (idle_slot_label side near far i)
        (congrArg side.opposite.place (idle_slot_x side near far i)))

theorem core_label (w : Fin (nested side near far p).wires) :
    (grouped side near far p).drawing.label (renameWires side near far p w) =
      (nested side near far p).drawing.label w := by
  obtain ⟨w, rfl⟩ := (nestedNames side near far p).surjective w
  rw [rename_at]
  exact (congrArg Prod.fst (grouped_data side near far p w 0)).trans
    (congrArg Prod.fst (nested_data side near far p w 0)).symm

theorem rename_ports (xs : List (Fin p.wires)) :
    xs.map (fun w => groupedNames side near far p (.inl w)) =
      (xs.map (fun w => nestedNames side near far p (.inl w))).map (renameWires side near far p) :=
  (congrArg (fun f => xs.map f) (funext fun w => (rename_at side near far p (.inl w)).symm)).trans
    (List.map_map ..).symm

theorem nested_inputs (j : Fin p.vertices) :
    (nested side near far p).drawing.inputs j =
      (p.drawing.inputs j).map (fun w => nestedNames side near far p (.inl w)) :=
  (drawing_inputs side far (inner side near p).drawing j).trans
    ((congrArg (List.map (Fin.castAdd far.profile.size)) (drawing_inputs side near p.drawing j)).trans
      ((List.map_map ..).trans
        (congrArg (fun f => (p.drawing.inputs j).map f) (funext fun w => (nested_active side near far p w).symm))))

theorem nested_outputs (j : Fin p.vertices) :
    (nested side near far p).drawing.outputs j =
      (p.drawing.outputs j).map (fun w => nestedNames side near far p (.inl w)) :=
  (drawing_outputs side far (inner side near p).drawing j).trans
    ((congrArg (List.map (Fin.castAdd far.profile.size)) (drawing_outputs side near p.drawing j)).trans
      ((List.map_map ..).trans
        (congrArg (fun f => (p.drawing.outputs j).map f) (funext fun w => (nested_active side near far p w).symm))))

def coreIncidence : (nested side near far p).drawing.IncidenceEquiv (grouped side near far p).drawing where
  vertex := Equiv.refl _
  wire := renameWires side near far p
  generator _ := rfl
  label := core_label side near far p
  inputs j := (drawing_inputs side (adjoin side near far) p.drawing j).trans
    ((rename_ports side near far p _).trans
      (congrArg (List.map (renameWires side near far p)) (nested_inputs side near far p j)).symm)
  outputs j := (drawing_outputs side (adjoin side near far) p.drawing j).trans
    ((rename_ports side near far p _).trans
      (congrArg (List.map (renameWires side near far p)) (nested_outputs side near far p j)).symm)

variable (g : ℝ → ℝ)
variable (onActive : ∀ x ∈ Set.Icc (0 : ℝ) 1, g (side.place (side.place x)) = side.place x)
variable (onNear : ∀ x ∈ Set.Icc (0 : ℝ) 1,
  g (side.place (side.opposite.place x)) = side.opposite.place (side.place x))
variable (onFar : ∀ x ∈ Set.Icc (0 : ℝ) 1, g (side.opposite.place x) = side.opposite.place (side.opposite.place x))

include onActive onNear onFar in
theorem core_x (w : Fin (nested side near far p).wires) (y : ℝ) (h : (nested side near far p).drawing.covers w y) :
    (grouped side near far p).drawing.x (renameWires side near far p w) y =
      g ((nested side near far p).drawing.x w y) := by
  obtain ⟨w, rfl⟩ := (nestedNames side near far p).surjective w
  rw [rename_at]
  have before := congrArg Prod.snd (nested_data side near far p w y)
  have after := congrArg Prod.snd (grouped_data side near far p w y)
  refine after.trans (Eq.trans ?_ (congrArg g before).symm)
  rcases w with i | (i | i)
  · have hi := (active_covers side (inner side near p).drawing far _ y).mp h
    have hp := (active_covers side p.drawing near i y).mp hi
    exact (onActive _ (Set.Ioo_subset_Icc_self (p.drawing.wire_inside i y hp))).symm
  · exact (onNear _ (Set.Ioo_subset_Icc_self (near.inside i))).symm
  · exact (onFar _ (Set.Ioo_subset_Icc_self (far.inside i))).symm

/-- The nested and grouped drawings have one shared incidence
comparison. The coordinate equations specify its action on each block. -/
def transport : CoreTransport g (nested side near far p) (grouped side near far p) where
  incidence := coreIncidence side near far p
  vertex_x j := (onActive _ (Set.Ioo_subset_Icc_self (p.drawing.vertex_inside j).1)).symm
  vertex_height _ := rfl
  wire_x := core_x side near far p g onActive onNear onFar

section Reverse

variable {a' b' : FixedCap S}
variable {d : FixedDrawing S a.profile b.profile} {e : FixedDrawing S a'.profile b'.profile}
variable {f fInv : ℝ → ℝ} (D : CoreTransport f d e) (inv : Function.LeftInverse fInv f)

/-- Invert a transport of the core incidence and coordinates. -/
def reverseTransport : CoreTransport fInv e d where
  incidence := CapClasses.incidence_symm D.incidence
  vertex_x j := by
    change d.drawing.vertexX (D.incidence.vertex.symm j) = _
    have h := D.vertex_x (D.incidence.vertex.symm j)
    rw [Equiv.apply_symm_apply] at h
    exact (inv _).symm.trans (congrArg fInv h).symm
  vertex_height j := by
    have h := D.vertex_height (D.incidence.vertex.symm j)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  wire_x w y h := by
    have cover := D.covers (D.incidence.wire.symm w) y
    rw [Equiv.apply_symm_apply] at cover
    have point := D.wire_x (D.incidence.wire.symm w) y (cover.mpr h)
    rw [Equiv.apply_symm_apply] at point
    exact (inv _).symm.trans (congrArg fInv point).symm

end Reverse

def horizontalInv : ℝ → ℝ := OrderedKnots.transfer rightKnots leftKnots

theorem horizontalInv_left : Function.LeftInverse horizontalInv horizontal :=
  OrderedKnots.transfer_inverse left_strict right_strict

theorem horizontalInv_right : Function.LeftInverse horizontal horizontalInv :=
  OrderedKnots.transfer_inverse right_strict left_strict

theorem horizontalInv_of_eq {x y : ℝ} (h : horizontal x = y) : horizontalInv y = x :=
  (congrArg horizontalInv h).symm.trans (horizontalInv_left x)

def leftTransport : CoreTransport horizontal (nested .left near far p) (grouped .left near far p) :=
  transport .left near far p horizontal
    (fun _ h => horizontal_left h) (fun _ h => horizontal_middle h) (fun _ h => horizontal_right h)

def rightTransport : CoreTransport horizontal (grouped .right near far p) (nested .right near far p) :=
  reverseTransport
    (transport .right near far p horizontalInv
      (fun _ h => horizontalInv_of_eq (horizontal_right h))
      (fun _ h => horizontalInv_of_eq (horizontal_middle h))
      (fun _ h => horizontalInv_of_eq (horizontal_left h)))
    horizontalInv_right

end Silmaril.RuntimeWires.Proofs.OuterAssociator
