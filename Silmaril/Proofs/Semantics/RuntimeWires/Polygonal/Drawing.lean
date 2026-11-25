module

public import Silmaril.Proofs.Semantics.RuntimeWires.Polygonal.Layers

public section

namespace Silmaril.RuntimeWires.Proofs.Polygonal

open Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {A B : List O} {S : Signature.{u,v} O}

theorem coordinate_ofCoordinates (x : Fin A.length → ℝ) (h : StrictMono x) (i : Fin A.length) :
    (Frontier.ofCoordinates x h).coordinate i = x i := by
  simp [Frontier.coordinate, Frontier.ofCoordinates]
  exact congrArg x (Fin.ext rfl)

theorem connector_cut (slab : Slab) (p q : Frontier A) {y : ℝ}
    (hy : y ∈ Set.Icc slab.lower slab.upper) :
    ∃ cut : Frontier A, ∀ i : Fin A.length,
      (connector slab p q i).trace ∩ {z : Point | z.2 = y} = {(cut.coordinate i, y)} := by
  obtain ⟨t, ht, ey⟩ := level_parameter slab hy
  let x := fun i : Fin A.length => interpolate (p.coordinate i) (q.coordinate i) t
  have ordered : StrictMono x := fun _ _ hij =>
    interpolate_strict (order_coordinates p hij) (order_coordinates q hij) ht
  refine ⟨Frontier.ofCoordinates x ordered, fun i => ?_⟩
  have point : (connector slab p q i).point t = ((Frontier.ofCoordinates x ordered).coordinate i, y) :=
    Prod.ext (coordinate_ofCoordinates x ordered i).symm ey
  ext z
  constructor
  · rintro ⟨⟨u, _, rfl⟩, hz⟩
    have time : u = t := (height_strict (connector slab p q i)).injective (hz.trans ey.symm)
    subst u
    exact point
  · intro hz
    change z = ((Frontier.ofCoordinates x ordered).coordinate i, y) at hz
    subst z
    exact ⟨⟨t, ht, point⟩, rfl⟩

private theorem connector_part_valid (slab : Slab) (p q : Frontier A) :
    (Part.connector slab p q).Valid := by
  refine ⟨List.pairwise_ofFn.mpr (fun {_ _} h => connector_disjoint slab p q (ne_of_lt h)), ?_⟩
  rintro z ⟨region, hr, hz⟩
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact trace_height hz

theorem drawing_valid {height : ℝ} (d : Drawing S height A B)
    {piece : Part} (h : piece ∈ d.parts) : piece.Valid := by
  induction d with
  | straight slab p =>
    have eq : piece = Part.connector slab p p := List.mem_singleton.mp h
    subst eq
    exact connector_part_valid slab p p
  | stack slab layer gap rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨layer_disjoint slab layer, fun p ⟨region, hr, hp⟩ => (layer_bounds layer hr hp).2⟩
    · rcases List.mem_cons.mp h with rfl | h
      · exact connector_part_valid ⟨slab.upper, _, gap⟩ layer.outputs.frontier rest.input
      · exact ih h

private theorem drawing_lower_bound {height : ℝ} (d : Drawing S height A B)
    {piece : Part} (h : piece ∈ d.parts) : height ≤ piece.slab.lower := by
  induction d with
  | straight slab p =>
    have eq : piece = Part.connector slab p p := List.mem_singleton.mp h
    subst eq
    exact le_rfl
  | stack slab layer gap rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_rfl
    · rcases List.mem_cons.mp h with rfl | h
      · exact slab.increasing.le
      · exact slab.increasing.le.trans (gap.le.trans (ih h))

theorem drawing_order {height : ℝ} (d : Drawing S height A B) :
    d.parts.Pairwise (fun earlier later => earlier.slab.upper ≤ later.slab.lower) := by
  induction d with
  | straight slab p => exact .cons (by simp) .nil
  | stack slab layer gap rest ih =>
    refine .cons ?_ (.cons ?_ ih)
    · intro piece h
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · exact gap.le.trans (drawing_lower_bound rest h)
    · intro piece h
      exact drawing_lower_bound rest h

theorem shared_cap {earlier later : Part} (he : earlier.Valid) (hl : later.Valid)
    (order : earlier.slab.upper ≤ later.slab.lower) {p : Point}
    (hp : earlier.Contains p) (hq : later.Contains p) :
    p.2 = earlier.slab.upper ∧ p.2 = later.slab.lower := by
  have a := (he.2 p hp).2
  have b := (hl.2 p hq).1
  exact ⟨le_antisymm a (order.trans b), le_antisymm (a.trans order) b⟩

theorem connector_entry {previous : Part} {slab : Slab} (h : previous.Valid)
    (order : previous.slab.upper ≤ slab.lower) (p q : Frontier A) (i : Fin A.length)
    {z : Point} (hp : previous.Contains z) (hc : z ∈ (connector slab p q i).trace) :
    z = (p.coordinate i, slab.lower) := by
  have lo := (trace_height hc).1
  have hi := (h.2 z hp).2.trans order
  exact lower_cap hc (le_antisymm hi lo)

theorem connector_exit {slab : Slab} {following : Part} (h : following.Valid)
    (order : slab.upper ≤ following.slab.lower) (p q : Frontier A) (i : Fin A.length)
    {z : Point} (hp : following.Contains z) (hc : z ∈ (connector slab p q i).trace) :
    z = (q.coordinate i, slab.upper) := by
  have hi := (trace_height hc).2
  have lo := order.trans (h.2 z hp).1
  exact upper_cap hc (le_antisymm hi lo)

end Silmaril.RuntimeWires.Proofs.Polygonal
