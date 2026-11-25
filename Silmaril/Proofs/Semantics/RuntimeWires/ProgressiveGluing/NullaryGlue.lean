module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialAssembly
public import Silmaril.Semantics.RuntimeWires.ProgressiveNullarySlide.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (height_left height_right x_right lower_inside unscale)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)
variable {v : Fin R} (s : upper.NullarySlide v)

theorem upper_interval {h : ℝ} (hh : h ∈ Set.Icc s.bottom s.top) :
    halfHeight 1 h ∈ Set.Icc (halfHeight 1 s.bottom) (halfHeight 1 s.top) :=
  ⟨(halfHeight_strictMono 1).monotone hh.1, (halfHeight_strictMono 1).monotone hh.2⟩

theorem upper_unscale_interval {h : ℝ}
    (hh : h ∈ Set.Icc (halfHeight 1 s.bottom) (halfHeight 1 s.top)) :
    slabHeight 1 h ∈ Set.Icc s.bottom s.top := by
  have a := hh.1
  have b := hh.2
  unfold halfHeight at a b
  unfold slabHeight
  exact ⟨by linarith, by linarith⟩

theorem above_middle {h : ℝ} (hh : halfHeight 1 s.bottom ≤ h) : 1 / 2 < h := by
  unfold halfHeight at hh
  linarith [s.bottom_pos]

/-- The upper slide preserves the cap matching itself. -/
def matchAtUpperHeight {h : ℝ} (hh : h ∈ Set.Icc s.bottom s.top) :
    lower.PartialVerticalMatch (s.atHeight h hh) where
  contact := m.contact
  label := m.label
  coordinate := m.coordinate

/-- The same empty vertical segment, in the rescaled upper slab. -/
noncomputable def liftUpper : (assemble m).NullarySlide (Fin.natAdd L v) where
  bottom := halfHeight 1 s.bottom
  top := halfHeight 1 s.top
  bottom_pos := (by norm_num : (0 : ℝ) < 1 / 2).trans (above_middle s le_rfl)
  ordered := halfHeight_strictMono 1 s.ordered
  top_lt_one := by unfold halfHeight; linarith [s.top_lt_one]
  no_inputs := by
    change S.source (gluedGenerator lower upper (Fin.natAdd L v)) = []
    rw [Proofs.ProgressiveGluing.generator_right]
    exact s.no_inputs
  no_outputs := by
    change S.target (gluedGenerator lower upper (Fin.natAdd L v)) = []
    rw [Proofs.ProgressiveGluing.generator_right]
    exact s.no_outputs
  wire_clear z h band cover := by
    let e := numbering lower upper
    have realCover : h ∈ Set.Icc (wireLo (e.symm z)) (wireHi m (e.symm z)) := cover
    have above := (above_middle s band.1).le
    obtain ⟨w, hw⟩ := upper_present m above realCover.2
    rw [← hw] at realCover
    change jointX m (e.symm z) h ≠ gluedVertexX lower upper (Fin.natAdd L v)
    rw [← hw, x_right]
    change (jointWire m (m.fromUpper w)).x h ≠ upper.vertexX v
    rw [x_fromUpper m w above]
    exact s.wire_clear w _ (upper_unscale_interval s band) ((covered_upper m w above).mp realCover)
  vertex_clear j ne band := by
    change gluedHeight lower upper j ∈ Set.Icc (halfHeight 1 s.bottom) (halfHeight 1 s.top) at band
    change gluedVertexX lower upper j ≠ gluedVertexX lower upper (Fin.natAdd L v)
    induction j using Fin.addCases with
    | left u =>
      rw [height_left] at band
      exact (((lower_inside (lower := lower) u).2.not_ge (above_middle s band.1).le)).elim
    | right u =>
      rw [height_right] at band
      rw [x_right, x_right]
      have other : u ≠ v := fun eq => ne (congrArg (Fin.natAdd L) eq)
      have localBand := upper_unscale_interval s band
      rw [unscale] at localBand
      exact s.vertex_clear u other localBand

private theorem wire_eq_of_x {a b : ℝ} {p q : Wire a b} (h : p.x = q.x) : p = q := by
  cases p
  cases q
  exact Wire.mk.injEq .. ▸ h

/-- The drawn coordinates and ordered port data determine the model. -/
theorem diagram_eq_of_data {V W : ℕ} {p q : Diagram S V W .point}
    (vx : p.vertexX = q.vertexX) (vy : p.vertexHeight = q.vertexHeight)
    (g : p.generator = q.generator) (lab : p.label = q.label)
    (st : p.start = q.start) (fn : p.finish = q.finish)
    (point : p.x = q.x) (input : HEq p.input q.input) (output : HEq p.output q.output) : p = q := by
  cases p
  cases q
  dsimp only at vx vy g lab st fn input output
  subst_vars
  have wires : _ = _ := funext fun w => wire_eq_of_x (congrFun point w)
  cases wires
  rfl

theorem liftUpper_atHeight {h : ℝ} (hh : h ∈ Set.Icc s.bottom s.top) :
    (liftUpper m s).atHeight (halfHeight 1 h) (upper_interval s hh) =
      assemble (matchAtUpperHeight m s hh) := by
  apply diagram_eq_of_data
  all_goals try rfl
  case vy =>
    funext j
    induction j using Fin.addCases with
    | left u =>
      rw [(liftUpper m s).stationary_height (upper_interval s hh) (Proofs.ProgressiveGluing.left_ne_right u v)]
      exact (height_left (lower := lower) (upper := upper) u).trans
        (height_left (lower := lower) (upper := s.atHeight h hh) u).symm
    | right u =>
      by_cases eq : u = v
      · subst u
        rw [(liftUpper m s).moved_height (upper_interval s hh)]
        change halfHeight 1 h = gluedHeight lower (s.atHeight h hh) (Fin.natAdd L v)
        rw [height_right, s.moved_height hh]
      · rw [(liftUpper m s).stationary_height (upper_interval s hh) (fun e => eq (Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))))]
        change gluedHeight lower upper (Fin.natAdd L u) =
          gluedHeight lower (s.atHeight h hh) (Fin.natAdd L u)
        rw [height_right, height_right, s.stationary_height hh eq]
  case lab =>
    funext z
    let e := numbering lower upper
    change wireLabel (upper := upper) (e.symm z) =
      wireLabel (upper := s.atHeight h hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl
  case st =>
    funext z
    let e := numbering lower upper
    change wireStart (upper := upper) (e.symm z) =
      wireStart (upper := s.atHeight h hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl
  case fn =>
    funext z
    let e := numbering lower upper
    change wireFinish m (e.symm z) = wireFinish (matchAtUpperHeight m s hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl
  case point =>
    funext z
    let e := numbering lower upper
    change jointX m (e.symm z) = jointX (matchAtUpperHeight m s hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl

theorem liftUpper_heightAt (t : NullarySlide.Time) :
    (liftUpper m s).heightAt t = halfHeight 1 (s.heightAt t) := by
  change (1 - t.val) * halfHeight 1 s.bottom + t.val * halfHeight 1 s.top = _
  unfold halfHeight NullarySlide.heightAt
  ring

theorem atHeight_congr {V W : ℕ} {d : Diagram S V W .point} {v : Fin V} (move : d.NullarySlide v)
    {a b : ℝ} (eq : a = b) (ha : a ∈ Set.Icc move.bottom move.top) (hb : b ∈ Set.Icc move.bottom move.top) :
    move.atHeight a ha = move.atHeight b hb := by
  subst b
  rfl

theorem liftUpper_frame (t : NullarySlide.Time) :
    (liftUpper m s).frame t = assemble (matchAtUpperHeight m s (s.height_mem t)) :=
  (atHeight_congr (liftUpper m s) (liftUpper_heightAt m s t) _ _).trans
    (liftUpper_atHeight m s (s.height_mem t))

end Silmaril.RuntimeWires.Proofs.PartialGluing
