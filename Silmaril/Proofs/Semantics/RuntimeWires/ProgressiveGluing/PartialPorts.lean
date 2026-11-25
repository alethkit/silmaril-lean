module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialDrawing
import Mathlib.Tactic.Linarith

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (height_left height_right lower_inside upper_inside unscale
  generator_left generator_right ports ports_left ports_right port_list_left port_list_right)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

def jointPorts (word : S.Edge → List O)
    (p : ∀ j, Fin (word (lower.generator j)).length → Fin A)
    (q : ∀ j, Fin (word (upper.generator j)).length → Fin B) :
    ∀ j, Fin (word (gluedGenerator lower upper j)).length → WireId lower upper :=
  ports word (fun j i => fromLower (p j i)) (fun j i => m.fromUpper (q j i))

abbrev jointInput := jointPorts m S.source lower.input upper.input
abbrev jointOutput := jointPorts m S.target lower.output upper.output

private theorem port_mem {X Y I : Type*} (f : X → Y) {p : I → X} {z : Y} :
    (∃ w, f w = z ∧ ∃ i, p i = w) ↔ ∃ i, f (p i) = z := by
  exact ⟨fun ⟨_, hw, i, hi⟩ => ⟨i, by rw [hi, hw]⟩, fun ⟨i, hi⟩ => ⟨_, hi, i, rfl⟩⟩

theorem input_exact (j : Fin (L + R)) (z : WireId lower upper) :
    wireFinish m z = some j ↔ ∃ i, jointInput m j i = z := by
  rw [← List.mem_ofFn]
  simp only [jointInput, jointPorts]
  induction j using Fin.addCases with
  | left v =>
    rw [finish_left_iff, port_list_left, List.mem_ofFn]
    simp only [lower.input_exact]
    exact port_mem fromLower
  | right v =>
    rw [finish_right_iff, port_list_right, List.mem_ofFn]
    simp only [upper.input_exact]
    exact port_mem m.fromUpper

theorem output_exact (j : Fin (L + R)) (z : WireId lower upper) :
    wireStart z = some j ↔ ∃ i, jointOutput m j i = z := by
  rw [← List.mem_ofFn]
  simp only [jointOutput, jointPorts]
  induction j using Fin.addCases with
  | left v =>
    rw [start_left_iff, port_list_left, List.mem_ofFn]
    simp only [lower.output_exact]
    exact port_mem fromLower
  | right v =>
    rw [start_right_iff, port_list_right, List.mem_ofFn]
    simp only [upper.output_exact]
    exact port_mem m.fromUpper

theorem port_types (word : S.Edge → List O)
    (p : ∀ j, Fin (word (lower.generator j)).length → Fin A)
    (q : ∀ j, Fin (word (upper.generator j)).length → Fin B)
    (hp : ∀ j, (List.ofFn (p j)).map lower.label = word (lower.generator j))
    (hq : ∀ j, (List.ofFn (q j)).map upper.label = word (upper.generator j))
    (j : Fin (L + R)) :
    (List.ofFn (jointPorts m word p q j)).map wireLabel = word (gluedGenerator lower upper j) := by
  induction j using Fin.addCases with
  | left v =>
    rw [jointPorts, port_list_left, generator_left]
    refine Eq.trans ?_ (hp v)
    simp only [List.map_ofFn, Function.comp_def]
    exact congrArg List.ofFn (funext fun i => label_fromLower (upper := upper) (p v i))
  | right v =>
    rw [jointPorts, port_list_right, generator_right]
    refine Eq.trans ?_ (hq v)
    simp only [List.map_ofFn, Function.comp_def]
    exact congrArg List.ofFn (funext fun i => label_fromUpper m (q v i))

theorem lo_at_output (j : Fin (L + R)) (i : Fin (S.target (gluedGenerator lower upper j)).length) :
    wireLo (jointOutput m j i) = gluedHeight lower upper j := by
  simp [wireLo, (output_exact m j _).mpr ⟨i, rfl⟩, endpointHeight]

theorem hi_at_input (j : Fin (L + R)) (i : Fin (S.source (gluedGenerator lower upper j)).length) :
    wireHi m (jointInput m j i) = gluedHeight lower upper j := by
  simp [wireHi, (input_exact m j _).mpr ⟨i, rfl⟩, endpointHeight]

private theorem left_coordinates (y : ℝ) (a b : Fin A)
    (slab : y < 1 / 2)
    (ha : y ∈ Set.Ioo (wireLo (fromLower a : WireId lower upper)) (wireHi m (fromLower a)))
    (hb : y ∈ Set.Ioo (wireLo (fromLower b : WireId lower upper)) (wireHi m (fromLower b)))
    (ordered : lower.crosses a (slabHeight 0 y) → lower.crosses b (slabHeight 0 y) →
      lower.x a (slabHeight 0 y) < lower.x b (slabHeight 0 y)) :
    (jointWire m (fromLower a)).x y < (jointWire m (fromLower b)).x y := by
  rw [x_fromLower m a slab.le, x_fromLower m b slab.le]
  exact ordered ((active_lower m a slab).mp ha) ((active_lower m b slab).mp hb)

private theorem right_coordinates (y : ℝ) (a b : Fin B)
    (slab : 1 / 2 < y)
    (ha : y ∈ Set.Ioo (wireLo (m.fromUpper a)) (wireHi m (m.fromUpper a)))
    (hb : y ∈ Set.Ioo (wireLo (m.fromUpper b)) (wireHi m (m.fromUpper b)))
    (ordered : upper.crosses a (slabHeight 1 y) → upper.crosses b (slabHeight 1 y) →
      upper.x a (slabHeight 1 y) < upper.x b (slabHeight 1 y)) :
    (jointWire m (m.fromUpper a)).x y < (jointWire m (m.fromUpper b)).x y := by
  rw [x_fromUpper m a slab.le, x_fromUpper m b slab.le]
  exact ordered ((active_upper m a slab).mp ha) ((active_upper m b slab).mp hb)

noncomputable def jointX (z : WireId lower upper) (y : ℝ) : ℝ :=
  (jointWire m z).x y

theorem input_order (j : Fin (L + R)) {i k : Fin (S.source (gluedGenerator lower upper j)).length}
    (order : i < k) {y : ℝ}
    (a : wireLo (jointInput m j i) < y) (b : wireLo (jointInput m j k) < y)
    (hy : y < gluedHeight lower upper j) :
    jointX m (jointInput m j i) y < jointX m (jointInput m j k) y := by
  have ia : y ∈ Set.Ioo (wireLo (jointInput m j i)) (wireHi m (jointInput m j i)) :=
    ⟨a, (hi_at_input m j i).symm ▸ hy⟩
  have ib : y ∈ Set.Ioo (wireLo (jointInput m j k)) (wireHi m (jointInput m j k)) :=
    ⟨b, (hi_at_input m j k).symm ▸ hy⟩
  induction j using Fin.addCases with
  | left v =>
    let i' := i.cast (congrArg (fun e => (S.source e).length) (generator_left v))
    let k' := k.cast (congrArg (fun e => (S.source e).length) (generator_left v))
    rw [height_left] at hy
    have slab := hy.trans (lower_inside (lower := lower) v).2
    simp only [jointInput, jointPorts, ports_left] at ia ib ⊢
    refine left_coordinates m y (lower.input v i') (lower.input v k') slab ia ib ?_
    intro h₁ h₂
    have below : slabHeight 0 y < lower.vertexHeight v := by
      unfold slabHeight halfHeight at *
      linarith
    exact lower.input_order v order h₁.1 h₂.1 below
  | right v =>
    let i' := i.cast (congrArg (fun e => (S.source e).length) (generator_right v))
    let k' := k.cast (congrArg (fun e => (S.source e).length) (generator_right v))
    rw [height_right] at hy
    let mid := ((1 / 2 : ℝ) + halfHeight 1 (upper.vertexHeight v)) / 2
    let z := max y mid
    have mid_low : 1 / 2 < mid := by dsimp [mid]; linarith [(upper_inside (upper := upper) v).1]
    have mid_high : mid < halfHeight 1 (upper.vertexHeight v) := by
      dsimp [mid]; linarith [(upper_inside (upper := upper) v).1]
    have zlow : 1 / 2 < z := mid_low.trans_le (le_max_right ..)
    have zhigh : z < halfHeight 1 (upper.vertexHeight v) := max_lt hy mid_high
    have za : z ∈ Set.Ioo (wireLo (jointInput m (Fin.natAdd L v) i))
        (wireHi m (jointInput m (Fin.natAdd L v) i)) :=
      ⟨a.trans_le (le_max_left ..), by rw [hi_at_input, height_right]; exact zhigh⟩
    have zb : z ∈ Set.Ioo (wireLo (jointInput m (Fin.natAdd L v) k))
        (wireHi m (jointInput m (Fin.natAdd L v) k)) :=
      ⟨b.trans_le (le_max_left ..), by rw [hi_at_input, height_right]; exact zhigh⟩
    refine order_across m za zb ia ib ?_
    change jointX m _ z < jointX m _ z
    simp only [jointInput, jointPorts, ports_right] at za zb ⊢
    refine right_coordinates m z (upper.input v i') (upper.input v k') zlow za zb ?_
    intro h₁ h₂
    have below : slabHeight 1 z < upper.vertexHeight v := by
      unfold slabHeight halfHeight at *
      linarith
    exact upper.input_order v order h₁.1 h₂.1 below

theorem output_order (j : Fin (L + R)) {i k : Fin (S.target (gluedGenerator lower upper j)).length}
    (order : i < k) {y : ℝ} (hy : gluedHeight lower upper j < y)
    (a : y < wireHi m (jointOutput m j i)) (b : y < wireHi m (jointOutput m j k)) :
    jointX m (jointOutput m j i) y < jointX m (jointOutput m j k) y := by
  have ia : y ∈ Set.Ioo (wireLo (jointOutput m j i)) (wireHi m (jointOutput m j i)) :=
    ⟨(lo_at_output m j i).symm ▸ hy, a⟩
  have ib : y ∈ Set.Ioo (wireLo (jointOutput m j k)) (wireHi m (jointOutput m j k)) :=
    ⟨(lo_at_output m j k).symm ▸ hy, b⟩
  induction j using Fin.addCases with
  | left v =>
    let i' := i.cast (congrArg (fun e => (S.target e).length) (generator_left v))
    let k' := k.cast (congrArg (fun e => (S.target e).length) (generator_left v))
    rw [height_left] at hy
    let mid := (halfHeight 0 (lower.vertexHeight v) + (1 / 2 : ℝ)) / 2
    let z := min y mid
    have mid_high : mid < 1 / 2 := by dsimp [mid]; linarith [(lower_inside (lower := lower) v).2]
    have mid_low : halfHeight 0 (lower.vertexHeight v) < mid := by
      dsimp [mid]; linarith [(lower_inside (lower := lower) v).2]
    have zhigh : z < 1 / 2 := (min_le_right ..).trans_lt mid_high
    have zlow : halfHeight 0 (lower.vertexHeight v) < z := lt_min hy mid_low
    have za : z ∈ Set.Ioo (wireLo (jointOutput m (Fin.castAdd R v) i))
        (wireHi m (jointOutput m (Fin.castAdd R v) i)) :=
      ⟨by rw [lo_at_output, height_left]; exact zlow, (min_le_left ..).trans_lt a⟩
    have zb : z ∈ Set.Ioo (wireLo (jointOutput m (Fin.castAdd R v) k))
        (wireHi m (jointOutput m (Fin.castAdd R v) k)) :=
      ⟨by rw [lo_at_output, height_left]; exact zlow, (min_le_left ..).trans_lt b⟩
    refine order_across m za zb ia ib ?_
    change jointX m _ z < jointX m _ z
    simp only [jointOutput, jointPorts, ports_left] at za zb ⊢
    refine left_coordinates m z (lower.output v i') (lower.output v k') zhigh za zb ?_
    intro h₁ h₂
    have above : lower.vertexHeight v < slabHeight 0 z := by
      unfold slabHeight halfHeight at *
      linarith
    exact lower.output_order v order above h₁.2 h₂.2
  | right v =>
    let i' := i.cast (congrArg (fun e => (S.target e).length) (generator_right v))
    let k' := k.cast (congrArg (fun e => (S.target e).length) (generator_right v))
    rw [height_right] at hy
    have slab := (upper_inside (upper := upper) v).1.trans hy
    simp only [jointOutput, jointPorts, ports_right] at ia ib ⊢
    refine right_coordinates m y (upper.output v i') (upper.output v k') slab ia ib ?_
    intro h₁ h₂
    have above : upper.vertexHeight v < slabHeight 1 y := by
      unfold slabHeight halfHeight at *
      linarith
    exact upper.output_order v order above h₁.2 h₂.2

end Silmaril.RuntimeWires.Proofs.PartialGluing
