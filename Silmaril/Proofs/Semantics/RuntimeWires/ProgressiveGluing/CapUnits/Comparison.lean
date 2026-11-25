module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Window
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapUnits

open ProgressiveGraph

def reflectHeight (top : Bool) : ℝ ≃ₜ ℝ where
  toFun := radius top
  invFun := radius top
  left_inv := radius_involutive top
  right_inv := radius_involutive top
  continuous_toFun := radius_continuous top
  continuous_invFun := radius_continuous top

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W V' W' : ℕ}

namespace Window

variable {d : ProgressiveGraph.Diagram S V W .point} {top : Bool} {a : CapProfile O} {p : Padding}
variable (c : Window d top a p)

def map : CapHomeomorph where
  plane :=
    let mirror := (Homeomorph.refl ℝ).prodCongr (reflectHeight top)
    (mirror.trans (p.radiusPlane c.knots_continuous c.knots_order)).trans mirror
  height := ((reflectHeight top).trans p.stretch).trans (reflectHeight top)
  increasing := by
    intro s t h
    change radius top (p.stretch (radius top s)) < radius top (p.stretch (radius top t))
    cases top
    · exact p.stretch_strict h
    · exact sub_lt_sub_left (p.stretch_strict (sub_lt_sub_left h 1)) 1
  height_eq _ := rfl
  outside z h := by
    change ((p.radiusPlane c.knots_continuous c.knots_order (z.1, radius top z.2)).1,
      radius top (p.radiusPlane c.knots_continuous c.knots_order (z.1, radius top z.2)).2) = z
    rw [p.radiusPlane_outside _ _ _ (radius_outside top h), radius_involutive]

theorem plane_radius (x y : ℝ) :
    c.map.plane (x, radius top y) =
      ((p.radiusPlane c.knots_continuous c.knots_order (x, y)).1, radius top (p.stretch y)) := by
  change ((p.radiusPlane c.knots_continuous c.knots_order (x, radius top (radius top y))).1,
    radius top (p.stretch (radius top (radius top y)))) = _
  rw [radius_involutive]

theorem plane_core (x : ℝ) {y : ℝ} (h : y ∈ Set.Icc p.width 1) :
    c.map.plane (x, radius top y) = (x, radius top (p.placed y)) := by
  rw [c.plane_radius, p.radiusPlane_core _ _ _ h, p.stretch_core h]

theorem plane_slot (i : Fin a.size) {y : ℝ} (h : y ∈ Set.Icc 0 p.width) :
    c.map.plane (d.x (c.slots i).val (radius top y), radius top y) =
      (d.x (c.slots i).val (radius top (p.clip (p.localHeight (p.stretch y)))),
        radius top (p.stretch y)) := by
  have eq : c.knots (p.clip y) i.succ = d.x (c.slots i).val (radius top y) := by
    simp only [knots, Fin.cases_succ, p.clip_eq h]
  rw [← eq, c.plane_radius, p.radiusPlane_slot _ _ i.succ]
  simp only [knots, Fin.cases_succ, p.clip_eq (p.clip_mem _)]

/-- Typed data and geometric inclusion for adding a constant trace segment
at one cap. The remaining drawing is affinely placed above that segment in
the coordinate measured from that cap. -/
structure Placed (e : ProgressiveGraph.Diagram S V' W' .point) where
  incidence : d.IncidenceEquiv e
  vertexX : ∀ j, e.vertexX (incidence.vertex j) = d.vertexX j
  height : ∀ j, e.vertexHeight (incidence.vertex j) =
    radius top (p.placed (radius top (d.vertexHeight j)))
  core : ∀ w y, d.covers w (radius top y) →
    (d.x w (radius top y), radius top (p.placed y)) ∈ (e.wire (incidence.wire w)).trace
  pad : ∀ (i : Fin a.size) y, y ∈ Set.Icc 0 p.amount →
    (a.x i, radius top y) ∈ (e.wire (incidence.wire (c.slots i).val)).trace

variable {c}
variable {e : ProgressiveGraph.Diagram S V' W' .point} (z : c.Placed e)

theorem placed_vertex (j : Fin V) :
    c.map.plane (d.vertexX j, d.vertexHeight j) =
      (e.vertexX (z.incidence.vertex j), e.vertexHeight (z.incidence.vertex j)) := by
  have span := radius_interior top (d.vertex_inside j).2
  have core := c.plane_core (d.vertexX j) ⟨(c.beyond j).le, span.2.le⟩
  rw [radius_involutive] at core
  rw [core, z.vertexX, z.height]

theorem placed_wire_point (w : Fin W) {y : ℝ} (cover : d.covers w (radius top y)) :
    c.map.plane (d.x w (radius top y), radius top y) ∈ (e.wire (z.incidence.wire w)).trace := by
  have unit := radius_unit top (CollarAssociator.covers_unit d cover)
  rw [radius_involutive] at unit
  by_cases hc : p.width ≤ y
  · rw [c.plane_core _ ⟨hc, unit.2⟩]
    exact z.core w y cover
  · have near : y ∈ Set.Icc 0 p.width := ⟨unit.1, le_of_not_ge hc⟩
    obtain ⟨i, rfl⟩ := c.from_cap near cover
    rw [c.plane_slot i near]
    rcases le_total (p.stretch y) p.amount with low | high
    · have hlocal : p.localHeight (p.stretch y) ≤ 0 := by
        have bound : p.stretch y ≤ p.placed 0 := p.placed_zero.symm ▸ low
        simpa only [p.local_placed] using p.local_strict.monotone bound
      rw [p.clip_low hlocal, c.coord]
      exact z.pad i _ ⟨(p.stretch_unit unit).1, low⟩
    · let t := p.localHeight (p.stretch y)
      have hlocal : t ∈ Set.Icc 0 p.width := ⟨p.local_nonneg high, p.local_le_width near.2⟩
      rw [p.clip_eq hlocal, ← p.placed_local (p.stretch y)]
      exact z.core _ t (c.cap_covers i hlocal)

theorem map_cap_height {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) : c.map.height y = y :=
  (c.map.height_eq (0, y)).symm.trans (congrArg Prod.snd (c.map.outside (0, y) h))

theorem placed_covers (w : Fin W) (y : ℝ) :
    e.covers (z.incidence.wire w) (c.map.height y) ↔ d.covers w y := by
  have lower : e.lower (z.incidence.wire w) = c.map.height (d.lower w) := by
    unfold ProgressiveGraph.Diagram.lower
    rw [z.incidence.start]
    cases hw : d.start w with
    | none => exact (c.map_cap_height (.inl le_rfl)).symm
    | some j => exact (congrArg Prod.snd (c.placed_vertex z j)).symm.trans (c.map.height_eq _)
  have upper : e.upper (z.incidence.wire w) = c.map.height (d.upper w) := by
    unfold ProgressiveGraph.Diagram.upper
    rw [z.incidence.finish]
    cases hw : d.finish w with
    | none => exact (c.map_cap_height (.inr le_rfl)).symm
    | some j => exact (congrArg Prod.snd (c.placed_vertex z j)).symm.trans (c.map.height_eq _)
  change c.map.height y ∈ Set.Icc (e.lower _) (e.upper _) ↔ y ∈ Set.Icc (d.lower w) (d.upper w)
  rw [lower, upper]
  simp only [Set.mem_Icc, c.map.increasing.le_iff_le]

theorem placed_trace (w : Fin W) :
    c.map.plane '' (d.wire w).trace = (e.wire (z.incidence.wire w)).trace := by
  have point (y : ℝ) (h : d.covers w y) :
      c.map.plane (d.x w y, y) ∈ (e.wire (z.incidence.wire w)).trace := by
    simpa only [radius_involutive] using
      placed_wire_point z (y := radius top y) (w := w) (by rwa [radius_involutive])
  ext q
  constructor
  · rintro ⟨_, ⟨y, covered, rfl⟩, rfl⟩
    exact point y covered
  · rintro ⟨t, covered, rfl⟩
    obtain ⟨y, rfl⟩ := c.map.height.surjective t
    have h := (placed_covers z w y).mp covered
    obtain ⟨t, _, eq⟩ := point y h
    have ht : t = c.map.height y := (congrArg Prod.snd eq).trans (c.map.height_eq _)
    subst t
    exact ⟨(d.x w y, y), ⟨y, h, rfl⟩, eq.symm⟩

def compare : d.CapComparison e where
  map := c.map
  incidence := z.incidence
  trace := placed_trace z
  vertex := placed_vertex z

end Window
end Silmaril.RuntimeWires.Proofs.CapUnits
