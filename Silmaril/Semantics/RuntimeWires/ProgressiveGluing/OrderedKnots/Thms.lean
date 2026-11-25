module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Homeomorph

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.OrderedKnots

variable {n : ℕ} {a b : Fin (n + 1) → ℝ}

theorem transfer_knot (ha : StrictMono a) (j : Fin (n + 1)) : transfer a b (a j) = b j :=
  Proofs.OrderedKnots.knot ha j

theorem transfer_segment (ha : StrictMono a) (j : Fin n) {x : ℝ}
    (hx : x ∈ Set.Icc (a j.castSucc) (a j.succ)) :
    transfer a b x = b j.castSucc +
      (b j.succ - b j.castSucc) * ((x - a j.castSucc) / (a j.succ - a j.castSucc)) :=
  Proofs.OrderedKnots.segment ha j hx

/-- Every point between the first and last knots lies in an affine piece. -/
theorem exists_segment (x : ℝ) (hx : a 0 < x) (hy : x ≤ a (Fin.last n)) :
    ∃ j : Fin n, x ∈ Set.Icc (a j.castSucc) (a j.succ) :=
  Proofs.OrderedKnots.covered x hx hy

theorem transfer_left (ha : StrictMono a) {x : ℝ} (h : x ≤ a 0) :
    transfer a b x = b 0 + (x - a 0) :=
  Proofs.OrderedKnots.left_tail ha h

theorem transfer_right (ha : StrictMono a) {x : ℝ} (h : a (Fin.last n) ≤ x) :
    transfer a b x = b (Fin.last n) + (x - a (Fin.last n)) :=
  Proofs.OrderedKnots.right_tail ha h

theorem transfer_strictMono (ha : StrictMono a) (hb : StrictMono b) : StrictMono (transfer a b) :=
  Proofs.OrderedKnots.transfer_strictMono ha hb

theorem transfer_self (ha : StrictMono a) (x : ℝ) : transfer a a x = x :=
  Proofs.OrderedKnots.transfer_self ha x

theorem transfer_inverse (ha : StrictMono a) (hb : StrictMono b) (x : ℝ) :
    transfer b a (transfer a b x) = x :=
  Proofs.OrderedKnots.inverse ha hb x

/-- The inverse is the same interpolation with the two knot lists exchanged. -/
noncomputable def homeomorph (ha : StrictMono a) (hb : StrictMono b) : ℝ ≃ₜ ℝ :=
  Proofs.OrderedKnots.homeomorph ha hb

theorem homeomorph_apply (ha : StrictMono a) (hb : StrictMono b) (x : ℝ) :
    homeomorph ha hb x = transfer a b x := by rfl

theorem homeomorph_symm_apply (ha : StrictMono a) (hb : StrictMono b) (x : ℝ) :
    (homeomorph ha hb).symm x = transfer b a x := by rfl

/-- The theorem applies jointly in all parameters, including the evaluation
point. Exchanging the knot lists gives joint continuity of the inverse. -/
theorem continuous_transfer {P : Type*} [TopologicalSpace P] {a b : P → Fin (n + 1) → ℝ}
    {x : P → ℝ} (ca : ∀ i, Continuous (fun p => a p i)) (cb : ∀ i, Continuous (fun p => b p i))
    (ha : ∀ p, StrictMono (a p)) (cx : Continuous x) :
    Continuous (fun p => transfer (a p) (b p) (x p)) :=
  Proofs.OrderedKnots.continuous_transfer ca cb ha cx

end Silmaril.RuntimeWires.ProgressiveGraph.OrderedKnots
