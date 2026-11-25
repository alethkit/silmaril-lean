module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.NullaryGlue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (height_left height_right x_left upper_inside unscale)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)
variable {v : Fin L} (s : lower.NullarySlide v)

theorem lower_interval {h : ℝ} (hh : h ∈ Set.Icc s.bottom s.top) :
    halfHeight 0 h ∈ Set.Icc (halfHeight 0 s.bottom) (halfHeight 0 s.top) :=
  ⟨(halfHeight_strictMono 0).monotone hh.1, (halfHeight_strictMono 0).monotone hh.2⟩

theorem lower_unscale_interval {h : ℝ}
    (hh : h ∈ Set.Icc (halfHeight 0 s.bottom) (halfHeight 0 s.top)) :
    slabHeight 0 h ∈ Set.Icc s.bottom s.top := by
  have a := hh.1
  have b := hh.2
  unfold halfHeight at a b
  unfold slabHeight
  exact ⟨by linarith, by linarith⟩

theorem below_middle {h : ℝ} (hh : h ≤ halfHeight 0 s.top) : h < 1 / 2 := by
  unfold halfHeight at hh
  linarith [s.top_lt_one]

def matchAtLowerHeight {h : ℝ} (hh : h ∈ Set.Icc s.bottom s.top) :
    (s.atHeight h hh).PartialVerticalMatch upper where
  contact := m.contact
  label := m.label
  coordinate := m.coordinate

noncomputable def liftLower : (assemble m).NullarySlide (Fin.castAdd R v) where
  bottom := halfHeight 0 s.bottom
  top := halfHeight 0 s.top
  bottom_pos := by unfold halfHeight; linarith [s.bottom_pos]
  ordered := halfHeight_strictMono 0 s.ordered
  top_lt_one := (below_middle s le_rfl).trans (by norm_num)
  no_inputs := by
    change S.source (gluedGenerator lower upper (Fin.castAdd R v)) = []
    rw [Proofs.ProgressiveGluing.generator_left]
    exact s.no_inputs
  no_outputs := by
    change S.target (gluedGenerator lower upper (Fin.castAdd R v)) = []
    rw [Proofs.ProgressiveGluing.generator_left]
    exact s.no_outputs
  wire_clear z h band cover := by
    let e := numbering lower upper
    have realCover : h ∈ Set.Icc (wireLo (e.symm z)) (wireHi m (e.symm z)) := cover
    have below := (below_middle s band.2).le
    obtain ⟨w, hw⟩ := lower_present below realCover.1
    rw [← hw] at realCover
    change jointX m (e.symm z) h ≠ gluedVertexX lower upper (Fin.castAdd R v)
    rw [← hw, x_left]
    change (jointWire m (fromLower w)).x h ≠ lower.vertexX v
    rw [x_fromLower m w below]
    exact s.wire_clear w _ (lower_unscale_interval s band) ((covered_lower m w below).mp realCover)
  vertex_clear j ne band := by
    change gluedHeight lower upper j ∈ Set.Icc (halfHeight 0 s.bottom) (halfHeight 0 s.top) at band
    change gluedVertexX lower upper j ≠ gluedVertexX lower upper (Fin.castAdd R v)
    induction j using Fin.addCases with
    | left u =>
      rw [height_left] at band
      rw [x_left, x_left]
      have other : u ≠ v := fun eq => ne (congrArg (Fin.castAdd R) eq)
      have localBand := lower_unscale_interval s band
      rw [unscale] at localBand
      exact s.vertex_clear u other localBand
    | right u =>
      rw [height_right] at band
      exact (((upper_inside (upper := upper) u).1.not_ge (below_middle s band.2).le)).elim

theorem liftLower_atHeight {h : ℝ} (hh : h ∈ Set.Icc s.bottom s.top) :
    (liftLower m s).atHeight (halfHeight 0 h) (lower_interval s hh) =
      assemble (matchAtLowerHeight m s hh) := by
  apply diagram_eq_of_data
  all_goals try rfl
  case vy =>
    funext j
    induction j using Fin.addCases with
    | left u =>
      by_cases eq : u = v
      · subst u
        rw [(liftLower m s).moved_height (lower_interval s hh)]
        change halfHeight 0 h = gluedHeight (s.atHeight h hh) upper (Fin.castAdd R v)
        rw [height_left, s.moved_height hh]
      · rw [(liftLower m s).stationary_height (lower_interval s hh) (fun e => eq (Fin.ext (congrArg (fun i : Fin (L + R) => i.val) e)))]
        change gluedHeight lower upper (Fin.castAdd R u) =
          gluedHeight (s.atHeight h hh) upper (Fin.castAdd R u)
        rw [height_left, height_left, s.stationary_height hh eq]
    | right u =>
      rw [(liftLower m s).stationary_height (lower_interval s hh)
        (Proofs.ProgressiveGluing.left_ne_right v u).symm]
      exact (height_right (lower := lower) (upper := upper) u).trans
        (height_right (lower := s.atHeight h hh) (upper := upper) u).symm
  case lab =>
    funext z
    let e := numbering lower upper
    change wireLabel (lower := lower) (e.symm z) =
      wireLabel (lower := s.atHeight h hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl
  case st =>
    funext z
    let e := numbering lower upper
    change wireStart (lower := lower) (e.symm z) =
      wireStart (lower := s.atHeight h hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl
  case fn =>
    funext z
    let e := numbering lower upper
    change wireFinish m (e.symm z) = wireFinish (matchAtLowerHeight m s hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl
  case point =>
    funext z
    let e := numbering lower upper
    change jointX m (e.symm z) = jointX (matchAtLowerHeight m s hh) (e.symm z)
    rcases e.symm z with w | (w | w) <;> rfl

theorem liftLower_heightAt (t : NullarySlide.Time) :
    (liftLower m s).heightAt t = halfHeight 0 (s.heightAt t) := by
  change (1 - t.val) * halfHeight 0 s.bottom + t.val * halfHeight 0 s.top = _
  unfold halfHeight NullarySlide.heightAt
  ring

theorem liftLower_frame (t : NullarySlide.Time) :
    (liftLower m s).frame t = assemble (matchAtLowerHeight m s (s.height_mem t)) :=
  (atHeight_congr (liftLower m s) (liftLower_heightAt m s t) _ _).trans
    (liftLower_atHeight m s (s.height_mem t))

end Silmaril.RuntimeWires.Proofs.PartialGluing
