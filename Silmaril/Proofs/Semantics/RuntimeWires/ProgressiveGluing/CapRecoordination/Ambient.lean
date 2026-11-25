module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapRecoordination.VertexFree
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Thms
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapRecoordination

open ProgressiveGraph OrderedKnots

universe u v

def clip (y : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 y), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clip_in {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) : (clip y).val = y := by
  change max 0 (min 1 y) = _
  rw [min_eq_right hy.2, max_eq_right hy.1]

theorem clip_continuous : Continuous clip :=
  Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id))
    _

variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}
variable (p : FixedDrawing S a b) (hp : p.vertices = 0)

def coords (y : ℝ) (i : Fin a.size) : ℝ :=
  p.drawing.x (inputWires p hp i) (clip y).val

theorem coords_inside (y : ℝ) (i : Fin a.size) : coords p hp y i ∈ Set.Ioo (0 : ℝ) 1 :=
  p.drawing.wire_inside _ _ ((covers p hp _ _).mpr (clip y).property)

def frameKnots (y : ℝ) : Fin (a.size + 2) → ℝ :=
  Fin.snoc (Fin.cons (0 : ℝ) (coords p hp y)) (1 : ℝ)

theorem first_knot (y : ℝ) : frameKnots p hp y 0 = 0 := by
  rw [show (0 : Fin (a.size + 2)) = (0 : Fin (a.size + 1)).castSucc from rfl,
    frameKnots, Fin.snoc_castSucc, Fin.cons_zero]

theorem last_knot (y : ℝ) : frameKnots p hp y (Fin.last (a.size + 1)) = 1 :=
  Fin.snoc_last _ _

theorem wire_knot (y : ℝ) (i : Fin a.size) :
    frameKnots p hp y i.succ.castSucc = coords p hp y i := by
  rw [frameKnots, Fin.snoc_castSucc, Fin.cons_succ]

theorem knots_strict (y : ℝ) : StrictMono (frameKnots p hp y) := by
  have middle : StrictMono (Fin.cons 0 (coords p hp y)) :=
    Fin.strictMono_cons.mpr ⟨fun i => (coords_inside p hp y i).1, ordered p hp (clip y).property⟩
  intro i j less
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact (lt_irrefl _ less).elim
    | cast i =>
      rw [last_knot]
      induction i using Fin.cases with
      | zero => exact (first_knot p hp y).trans_lt zero_lt_one
      | succ i => rw [wire_knot]; exact (coords_inside p hp y i).2
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact ((Fin.le_last j.castSucc).not_gt less).elim
    | cast i =>
      simpa only [frameKnots, Fin.snoc_castSucc] using middle (Fin.castSucc_lt_castSucc_iff.mp less)

theorem knots_continuous (i : Fin (a.size + 2)) : Continuous (fun y => frameKnots p hp y i) := by
  induction i using Fin.lastCases with
  | last => simpa only [last_knot] using (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
  | cast i =>
    induction i using Fin.cases with
    | zero =>
      simpa only [show (0 : Fin (a.size + 1)).castSucc = 0 from rfl, first_knot]
        using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
    | succ i =>
      simp only [wire_knot, coords]
      exact (wire_continuous p hp (inputWires p hp i)).domRestrict.comp clip_continuous

variable (q : FixedDrawing S a b) (hq : q.vertices = 0)

theorem same_cap_knots {y : ℝ} (hy : y ≤ 0 ∨ 1 ≤ y) :
    frameKnots p hp y = frameKnots q hq y := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [last_knot, last_knot]
  | cast i =>
    induction i using Fin.cases with
    | zero => rw [show (0 : Fin (a.size + 1)).castSucc = 0 from rfl, first_knot, first_knot]
    | succ i =>
      rw [wire_knot, wire_knot, coords, coords]
      rcases hy with low | high
      · have h : (clip y).val = 0 := max_eq_left ((min_le_right _ _).trans low)
        rw [h]
        exact (p.input_x i).trans (q.input_x i).symm
      · have h : (clip y).val = 1 := by
          change max 0 (min 1 y) = 1
          rw [min_eq_left high, max_eq_right zero_le_one]
        rw [h]
        exact same_top p hp q hq i

def fibreMap (z : ℝ × ℝ) : ℝ × ℝ :=
  (transfer (frameKnots p hp z.2) (frameKnots q hq z.2) z.1, z.2)

theorem fibreMap_continuous : Continuous (fibreMap p hp q hq) :=
  (continuous_transfer (fun i => (knots_continuous p hp i).comp continuous_snd)
    (fun i => (knots_continuous q hq i).comp continuous_snd)
    (fun z => knots_strict p hp z.2) continuous_fst).prodMk continuous_snd

theorem fibreMap_inverse (z : ℝ × ℝ) : fibreMap q hq p hp (fibreMap p hp q hq z) = z :=
  Prod.ext (transfer_inverse (knots_strict p hp z.2) (knots_strict q hq z.2) z.1) rfl

def ambient : CapHomeomorph where
  plane :=
    { toFun := fibreMap p hp q hq
      invFun := fibreMap q hq p hp
      left_inv := fibreMap_inverse p hp q hq
      right_inv := fibreMap_inverse q hq p hp
      continuous_toFun := fibreMap_continuous p hp q hq
      continuous_invFun := fibreMap_continuous q hq p hp }
  height := Homeomorph.refl _
  increasing := strictMono_id
  height_eq _ := rfl
  outside z h := by
    change (transfer (frameKnots p hp z.2) (frameKnots q hq z.2) z.1, z.2) = z
    rw [← same_cap_knots p hp q hq h, transfer_self (knots_strict p hp z.2)]

theorem increasing_fibre (y : ℝ) :
    StrictMono (fun x => ((ambient p hp q hq).plane (x, y)).1) :=
  transfer_strictMono (knots_strict p hp y) (knots_strict q hq y)

theorem ambient_outside_sides (z : ℝ × ℝ) (h : z.1 ≤ 0 ∨ 1 ≤ z.1) :
    (ambient p hp q hq).plane z = z := by
  refine Prod.ext ?_ rfl
  change transfer (frameKnots p hp z.2) (frameKnots q hq z.2) z.1 = z.1
  rcases h with low | high
  · rw [transfer_left (knots_strict p hp z.2) (by rwa [first_knot]), first_knot, first_knot,
      sub_zero, zero_add]
  · rw [transfer_right (knots_strict p hp z.2) (by rwa [last_knot]), last_knot, last_knot]
    linarith

theorem ambient_point (i : Fin a.size) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (ambient p hp q hq).plane (p.drawing.x (inputWires p hp i) y, y) =
      (q.drawing.x (inputWires q hq i) y, y) := by
  have knot (d : FixedDrawing S a b) (hd : d.vertices = 0) :
      frameKnots d hd y i.succ.castSucc = d.drawing.x (inputWires d hd i) y := by
    rw [wire_knot, coords, clip_in hy]
  refine Prod.ext ?_ rfl
  change transfer (frameKnots p hp y) (frameKnots q hq y)
    (p.drawing.x (inputWires p hp i) y) = _
  rw [← knot p hp, transfer_knot (knots_strict p hp y), knot q hq]

end Silmaril.RuntimeWires.Proofs.CapRecoordination
