module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.Thms
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Coherence.Defs
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.HorizontalPlacement.Thms
import Silmaril.Semantics.RuntimeWires.Presentation.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.RuntimeReadout.Regression

open CategoryTheory Presentation ProgressiveGraph
open scoped MonoidalCategory

private abbrev effects : EffectfulPolygraph where
  Obj := Unit
  pure := Signature.empty Unit
  effect :=
    { Edge := Bool
      source _ := []
      target _ := [] }

private def runtimeCap : FixedRuntimeCap effects where
  cap :=
    { profile :=
        { size := 1
          label _ := none
          x _ := 1 / 3
          ordered := fun {i j} lt => (lt.ne (Subsingleton.elim i j)).elim }
      inside _ := by norm_num [Set.mem_Ioo] }
  word := []
  types := rfl

private def start (w : Fin 2) : Option (Fin 1) := if w = 0 then none else some 0
private def finish (w : Fin 2) : Option (Fin 1) := if w = 0 then some 0 else none

private def strand (w : Fin 2) :
    ProgressiveGraph.Wire (endpointHeight (fun _ => 1 / 2) 0 (start w))
      (endpointHeight (fun _ => 1 / 2) 1 (finish w)) where
  x _ := 1 / 3
  increasing := by fin_cases w <;> norm_num [start, finish, endpointHeight]
  continuous := continuousOn_const
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    ring

/-- One effect consumes the lower runtime strand and returns the upper one. -/
private def effectDiagram (e : Bool) : ProgressiveGraph.Diagram (signature effects) 1 2 .point where
  vertexX _ := 1 / 3
  vertexHeight _ := 1 / 2
  vertex_inside _ := by norm_num [Set.mem_Ioo]
  vertex_separation := fun {_ _} _ => Subsingleton.elim _ _
  generator _ := .effect e
  label _ := none
  start := start
  finish := finish
  wire := strand
  wire_inside _ _ _ := by norm_num [strand, Set.mem_Ioo]
  start_attached _ _ _ := rfl
  finish_attached _ _ _ := rfl
  separated := by
    intro i j ne y hy hz
    fin_cases i <;> fin_cases j <;>
      norm_num [start, finish, endpointHeight, Set.mem_Ioo, Set.mem_Icc] at *
    all_goals linarith
  avoids_vertex i _ h := by
    fin_cases i <;> norm_num [start, finish, endpointHeight, Set.mem_Ioo] at h
  input_boundary_separated := by
    intro i j ne hi hj
    fin_cases i <;> fin_cases j <;> simp [start] at *
  output_boundary_separated := by
    intro i j ne hi hj
    fin_cases i <;> fin_cases j <;> simp [finish] at *
  input _ _ := 0
  output _ _ := 1
  input_exact := by
    intro v w
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases w <;> simp [finish, signature, effects]
  output_exact := by
    intro v w
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    fin_cases w <;> simp [start, signature, effects]
  input_types _ := rfl
  output_types _ := rfl
  input_order _ {i j} lt := (lt.ne (Subsingleton.elim (α := Fin 1) i j)).elim
  output_order _ {i j} lt := (lt.ne (Subsingleton.elim (α := Fin 1) i j)).elim

private def generatorDrawing (e : Bool) :
    FixedDrawing (signature effects) runtimeCap.cap.profile runtimeCap.cap.profile where
  vertices := 1
  wires := 2
  drawing := effectDiagram e
  input :=
    { toFun _ := ⟨0, rfl⟩
      invFun _ := (0 : Fin 1)
      left_inv i := Subsingleton.elim (α := Fin 1) _ i
      right_inv w := by
        apply Subtype.ext
        have h := w.property
        change start w.val = none at h
        simpa [start, eq_comm] using h }
  output :=
    { toFun _ := ⟨1, rfl⟩
      invFun _ := (0 : Fin 1)
      left_inv i := Subsingleton.elim (α := Fin 1) _ i
      right_inv w := by
        apply Subtype.ext
        have h := w.property
        change finish w.val = none at h
        have ne : w.val ≠ 0 := by simpa [finish] using h
        have bound := w.val.isLt
        apply Fin.ext
        change 1 = w.val.val
        by_contra! notOne
        exact ne (Fin.ext (by omega)) }
  input_label _ := rfl
  output_label _ := rfl
  input_x _ := rfl
  output_x _ := rfl

private def geometricEffect (e : Bool) : runtimeCap ⟶ runtimeCap :=
  FixedRuntimeCap.ofDrawing (generatorDrawing e)

private def readout := FixedRuntimeCap.toComputations effects

private theorem effect_noThrough (e : Bool) (w : Fin 2) : ¬ (effectDiagram e).crosses w (1 / 2) := by
  fin_cases w <;> norm_num [ProgressiveGraph.Diagram.crosses, ProgressiveGraph.Diagram.lower,
    ProgressiveGraph.Diagram.upper, effectDiagram, start, finish, endpointHeight, Set.mem_Ioo]

private theorem read_effect (e : Bool) : readout.map (geometricEffect e) = Computations.effect e := by
  have h := FixedRuntimeCap.map_effect (X := runtimeCap) (Y := runtimeCap) e
    (generatorDrawing e) (0 : Fin 1) (fun _ => Subsingleton.elim (α := Fin 1) _ _) rfl (effect_noThrough e) rfl rfl
  refine h.trans ?_
  change 𝟙 runtimeCap.computation ≫ Computations.effect e ≫ 𝟙 runtimeCap.computation = _
  erw [Category.id_comp, Category.comp_id]

private abbrev effectTerm (e : Bool) : Diagram (signature effects) [none] [none] :=
  .gen (S := signature effects) (Edge.effect e)

/-- Collared composition retains the order on the one shared runtime wire. -/
private theorem read_composite (e f : Bool) :
    ((FixedRuntimeCap.readClique (geometricEffect e ≫ geometricEffect f)).app 0 0) =
      Diagram.Presented.ofTerm (E := Relations effects) (.comp (effectTerm e) (effectTerm f)) := by
  rw [FixedRuntimeCap.readClique_leftmost]
  have h := (readout.map_comp (geometricEffect e) (geometricEffect f)).trans
    (congrArg₂ (· ≫ ·) (read_effect e) (read_effect f))
  exact h

example :
    (FixedRuntimeCap.readClique (X := runtimeCap) (Y := runtimeCap) (FixedRuntimeCap.ofDrawing
      ((generatorDrawing false).thenDo (generatorDrawing true)))).app 0 0 =
      Diagram.Presented.ofTerm (E := Relations effects) (.comp (effectTerm false) (effectTerm true)) := by
  have glued : geometricEffect false ≫ geometricEffect true =
      FixedRuntimeCap.ofDrawing ((generatorDrawing false).thenDo (generatorDrawing true)) :=
    FixedCap.comp_drawings (a := runtimeCap.cap) (b := runtimeCap.cap) (c := runtimeCap.cap)
      (generatorDrawing false) (generatorDrawing true)
  exact (congrArg (fun f : runtimeCap ⟶ runtimeCap => (FixedRuntimeCap.readClique f).app 0 0)
    glued).symm.trans (read_composite false true)

private def events : {A B : List (Presentation.Wire effects.Obj)} →
    Diagram (signature effects) A B → List Bool
  | _, _, .id _ => []
  | _, _, .gen (Edge.effect e) => [e]
  | _, _, .gen (Edge.pure e) => e.elim
  | _, _, .gen (Edge.moveLeft _) => []
  | _, _, .gen (Edge.moveRight _) => []
  | _, _, .comp f g => events f ++ events g
  | _, _, .tensor f g => events f ++ events g

private theorem events_reindex {A B C D : List (Presentation.Wire effects.Obj)}
    (f : Diagram (signature effects) A B) (a : A = C) (b : B = D) :
    events (f.reindex a b) = events f := by
  cases a
  cases b
  rfl

private theorem count_append (A B : List (Presentation.Wire effects.Obj)) :
    runtimeCount (A ++ B) = runtimeCount A + runtimeCount B := by
  simp [runtimeCount, List.filter_append]

private theorem events_zero {A B : List (Presentation.Wire effects.Obj)}
    (f : Diagram (signature effects) A B) : runtimeCount A = 0 → events f = [] := by
  induction f with
  | id => intro _; rfl
  | gen e =>
    intro empty
    cases e with
    | effect => simp [runtimeCount] at empty
    | pure e => exact e.elim
    | moveLeft _ => rfl
    | moveRight _ => rfl
  | comp f g ih ig =>
    intro empty
    simp only [events, ih empty, ig ((preservesRuntime f).symm.trans empty), List.append_nil]
  | tensor f g ih ig =>
    intro empty
    rw [count_append] at empty
    simp only [events, ih (by omega), ig (by omega), List.append_nil]

/-- The order of effect labels is invariant on the one-runtime part of
the actual term quotient. Interchange has an event-free tensor factor. -/
private theorem events_congr {A B : List (Presentation.Wire effects.Obj)}
    {f g : Diagram (signature effects) A B} (h : Diagram.Congruence (Relations effects) f g) :
    runtimeCount A ≤ 1 → events f = events g := by
  induction h with
  | equation h =>
    intro _
    cases h with
    | cancelRight _ => rfl
    | cancelLeft _ => rfl
    | pureRight e => exact e.elim
    | pureLeft e => exact e.elim
  | refl => intro _; rfl
  | symm _ ih => intro fits; exact (ih fits).symm
  | trans _ _ ih ig => intro fits; exact (ih fits).trans (ig fits)
  | @comp A B _ f _ _ _ _ _ ih ig =>
    intro fits
    simp only [events, ih fits, ig ((preservesRuntime f) ▸ fits)]
  | tensor _ _ ih ig =>
    intro fits
    rw [count_append] at fits
    simp only [events, ih (by omega), ig (by omega)]
  | id_comp => intro _; simp [events]
  | comp_id => intro _; simp [events]
  | comp_assoc => intro _; simp [events, List.append_assoc]
  | tensor_id => intro _; rfl
  | @tensor_comp A B C D F H f g h k =>
    intro fits
    rw [count_append] at fits
    by_cases left : runtimeCount A = 0
    · have second := (preservesRuntime f).symm.trans left
      simp [events, events_zero f left, events_zero g second]
    · have right : runtimeCount D = 0 := by omega
      have second := (preservesRuntime h).symm.trans right
      simp [events, events_zero h right, events_zero k second]
  | tensor_unit_left f =>
    intro _
    exact (events_reindex (.tensor (.id []) f) _ _).trans (List.nil_append _)
  | tensor_unit_right f =>
    intro _
    exact (events_reindex (.tensor f (.id [])) _ _).trans (List.append_nil _)
  | tensor_assoc f g h =>
    intro _
    exact (events_reindex (.tensor (.tensor f g) h) _ _).trans (List.append_assoc _ _ _)

example :
    ((FixedRuntimeCap.readClique (geometricEffect false ≫ geometricEffect true)).app 0 0) ≠
      ((FixedRuntimeCap.readClique (geometricEffect true ≫ geometricEffect false)).app 0 0) := by
  rw [read_composite, read_composite]
  intro same
  have relation := Quotient.exact same
  have labels := events_congr relation (by decide)
  change [false, true] = [true, false] at labels
  contradiction

private def idleCap : FixedCap (signature effects) where
  profile :=
    { size := 1
      label _ := some ()
      x _ := 1 / 3
      ordered := fun {i j} lt => (lt.ne (Subsingleton.elim i j)).elim }
  inside _ := by norm_num [Set.mem_Ioo]

private theorem idle_types : idleCap.types = values [()] := rfl

example (e : Bool) :
    readout.map (X := runtimeCap.padRight idleCap idle_types) (Y := runtimeCap.padRight idleCap idle_types)
      (show runtimeCap.padRight idleCap idle_types ⟶ runtimeCap.padRight idleCap idle_types from
        (show runtimeCap.cap ⟶ runtimeCap.cap from geometricEffect e) ▷ idleCap) =
    (Computations.whiskerRight (Computations.mk (G := effects) [()])).map (Computations.effect (G := effects) e) :=
  (FixedRuntimeCap.toComputations_padRight idleCap idle_types (geometricEffect e)).trans
    (congrArg (Computations.whiskerRight (Computations.mk (G := effects) [()])).map (read_effect e))

private def effectOnRight : PositionedRuntimeCap effects where
  cap := idleCap.beside runtimeCap.cap
  word := [()]
  position := 1
  types := FixedCap.beside_labels idleCap runtimeCap.cap

private def placedEffect (e : Bool) : effectOnRight.cap ⟶ effectOnRight.cap :=
  idleCap ◁ (show runtimeCap.cap ⟶ runtimeCap.cap from geometricEffect e)

private abbrev placedDrawing (e : Bool) :=
  ActiveStrip.right.placeDrawing (a := runtimeCap.cap) (b := runtimeCap.cap)
    (generatorDrawing e) idleCap

private theorem placedEffect_drawing (e : Bool) :
    placedEffect e = FixedCap.ofDrawing (a := effectOnRight.cap) (b := effectOnRight.cap)
      (placedDrawing e) := by
  change (ActiveStrip.right.whisker idleCap).map (FixedCap.ofDrawing (generatorDrawing e)) = _
  exact ActiveStrip.right.whisker_drawings (a := runtimeCap.cap) (b := runtimeCap.cap) idleCap
    (generatorDrawing e)

example (e : Bool) : (placedDrawing e).drawing.vertexX (0 : Fin 1) = 2 / 3 := by
  change ActiveStrip.right.place (1 / 3 : ℝ) = _
  norm_num [ActiveStrip.place]

private theorem placed_component (e : Bool) :
    PositionedRuntimeCap.component (X := effectOnRight) (Y := effectOnRight) (placedEffect e) =
      valueWord (G := effects) [()] ◁ (Computations.inRuntime effects).map (Computations.effect (G := effects) e) := by
  have read := FixedCap.runtimeSweep_generator (A := runtimeCap.cap) (B := runtimeCap.cap) (Edge.effect e)
    (generatorDrawing e) (0 : Fin 1) (fun _ => Subsingleton.elim (α := Fin 1) _ _) rfl
    (effect_noThrough e) rfl rfl
  change effectOnRight.boundaryIso.inv ≫
    (FixedCap.runtimeSweep effects).map (idleCap ◁ FixedCap.ofDrawing (generatorDrawing e)) ≫
      effectOnRight.boundaryIso.hom = _
  erw [FixedCap.runtimeSweep_padLeft, read]
  change (𝟙 (placed (G := effects) [()] 1)) ≫
    ((𝟙 (placed (G := effects) [()] 1)) ≫ valueWord (G := effects) [()] ◁
      ((𝟙 (runtime effects)) ≫ (Computations.inRuntime effects).map (Computations.effect (G := effects) e) ≫
        𝟙 (runtime effects)) ≫ 𝟙 (placed (G := effects) [()] 1)) ≫
      𝟙 (placed (G := effects) [()] 1) = _
  repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

/-- The effect is drawn to the right of the value strand. The leftmost
component transports its independently read component using the two braidings. -/
example (e : Bool) :
    (PositionedRuntimeCap.readClique (X := effectOnRight) (Y := effectOnRight) (placedEffect e)).app 0 0 =
      ((braidClique (G := effects) [()]).braid 0 1).hom ≫
        (valueWord [()] ◁ (Computations.inRuntime effects).map (Computations.effect (G := effects) e)) ≫
        ((braidClique (G := effects) [()]).braid 0 1).inv := by
  erw [PositionedRuntimeCap.readClique_leftmost, placed_component]
  rfl

private abbrev innerCap := idleCap.beside runtimeCap.cap

private def outsideCap : FixedCap (signature effects) where
  profile :=
    { size := 2
      label i := if i.val = 0 then none else some ()
      x i := if i.val = 0 then 1 / 6 else 2 / 3
      ordered := by
        intro i j lt
        fin_cases i <;> fin_cases j <;> norm_num at * }
  inside i := by fin_cases i <;> norm_num [Set.mem_Ioo]

private def crossCap (runtimeOnRight : Bool) : FixedCap (signature effects) :=
  if runtimeOnRight then innerCap else outsideCap

private theorem crossSize (r : Bool) : (crossCap r).profile.size = 2 := by
  cases r <;> rfl

private def gateEdge (r : Bool) : Edge effects :=
  if r then .moveRight () else .moveLeft ()

private def gateStart (i : Fin 4) : Option (Fin 1) :=
  if i.val < 2 then none else some 0

private def gateFinish (i : Fin 4) : Option (Fin 1) :=
  if i.val < 2 then some 0 else none

private def gateX (i : Fin 4) (y : ℝ) : ℝ :=
  if i.val = 0 ∨ i.val = 3 then 1 / 6 + y / 2 else 2 / 3 - y / 2

private def gateLabel (r : Bool) (i : Fin 4) : Presentation.Wire effects.Obj :=
  if (i.val = 0 ∨ i.val = 3) ↔ r = true then none else some ()

private def gateWire (i : Fin 4) : ProgressiveGraph.Wire
    (endpointHeight (fun _ => 1 / 2) 0 (gateStart i))
    (endpointHeight (fun _ => 1 / 2) 1 (gateFinish i)) where
  x := gateX i
  increasing := by fin_cases i <;> norm_num [gateStart, gateFinish, endpointHeight]
  continuous := by
    unfold gateX
    split
    · exact (continuous_const.add (continuous_id.div_const _)).continuousOn
    · exact (continuous_const.sub (continuous_id.div_const _)).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold gateX
    split <;> ring

private def gateIn (r : Bool) (i : Fin ((signature effects).source (gateEdge r)).length) : Fin 4 :=
  ⟨i.val, by
    have bound := i.isLt
    cases r <;> change i.val < 2 at bound <;> omega⟩

private def gateOut (r : Bool) (i : Fin ((signature effects).target (gateEdge r)).length) : Fin 4 :=
  ⟨i.val + 2, by
    have bound := i.isLt
    cases r <;> change i.val < 2 at bound <;> omega⟩

/-- The two incoming and two outgoing polygonal segments meet only at the
crossing generator, with the runtime label exchanged between the two slots. -/
private def gate (r : Bool) : ProgressiveGraph.Diagram (signature effects) 1 4 .point where
  vertexX _ := 5 / 12
  vertexHeight _ := 1 / 2
  vertex_inside _ := by norm_num [Set.mem_Ioo]
  vertex_separation := fun {_ _} _ => Subsingleton.elim _ _
  generator _ := gateEdge r
  label := gateLabel r
  start := gateStart
  finish := gateFinish
  wire := gateWire
  wire_inside := by
    intro i y h
    fin_cases i <;> norm_num [gateWire, gateX, gateStart, gateFinish, endpointHeight, Set.mem_Ioo] at *
    all_goals constructor <;> linarith [h.1, h.2]
  start_attached i _ _ := by fin_cases i <;> norm_num [gateWire, gateX]
  finish_attached i _ _ := by fin_cases i <;> norm_num [gateWire, gateX]
  separated := by
    intro i j ne y hi hj
    fin_cases i <;> fin_cases j <;>
      norm_num [gateWire, gateX, gateStart, gateFinish, endpointHeight, Set.mem_Ioo, Set.mem_Icc] at *
    all_goals linarith [hi.1, hi.2, hj.1, hj.2]
  avoids_vertex i _ h := by
    fin_cases i <;> norm_num [gateStart, gateFinish, endpointHeight, Set.mem_Ioo] at h
  input_boundary_separated := by
    intro i j ne hi hj
    fin_cases i <;> fin_cases j <;> norm_num [gateStart, gateWire, gateX] at *
  output_boundary_separated := by
    intro i j ne hi hj
    fin_cases i <;> fin_cases j <;> norm_num [gateFinish, gateWire, gateX] at *
  input _ := gateIn r
  output _ := gateOut r
  input_exact := by
    intro v i
    obtain rfl : v = 0 := Subsingleton.elim _ _
    change gateFinish i = some 0 ↔ ∃ j, gateIn r j = i
    have size : ((signature effects).source (gateEdge r)).length = 2 := by cases r <;> rfl
    constructor
    · intro h
      have inside : i.val < 2 := by
        unfold gateFinish at h
        split at h
        · assumption
        · cases h
      exact ⟨⟨i.val, size.symm ▸ inside⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      have inside : j.val < 2 := size ▸ j.isLt
      simp [gateFinish, gateIn, inside]
  output_exact := by
    intro v i
    obtain rfl : v = 0 := Subsingleton.elim _ _
    change gateStart i = some 0 ↔ ∃ j, gateOut r j = i
    have size : ((signature effects).target (gateEdge r)).length = 2 := by cases r <;> rfl
    constructor
    · intro h
      have lower : 2 ≤ i.val := by
        unfold gateStart at h
        split at h
        · cases h
        · omega
      have upper := i.isLt
      refine ⟨⟨i.val - 2, by rw [size]; omega⟩, Fin.ext ?_⟩
      change i.val - 2 + 2 = i.val
      omega
    · rintro ⟨j, rfl⟩
      simp [gateStart, gateOut]
  input_types _ := by cases r <;> rfl
  output_types _ := by cases r <;> rfl
  input_order := by
    intro v i j less y hi hj hy
    cases r <;> change Fin 2 at i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [gateIn, gateWire, gateX] at *
    all_goals linarith
  output_order := by
    intro v i j less y hy hi hj
    cases r <;> change Fin 2 at i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [gateOut, gateWire, gateX] at *
    all_goals linarith

private def lowerSlots (r : Bool) : Fin 2 ≃ {w : Fin 4 // (gate r).start w = none} where
  toFun i := ⟨i.castAdd 2, by
    change gateStart (i.castAdd 2) = none
    simp [gateStart, i.isLt]⟩
  invFun w := ⟨w.val.val, by
    have hw := w.property
    change gateStart w.val = none at hw
    simpa [gateStart] using hw⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)

private def upperSlots (r : Bool) : Fin 2 ≃ {w : Fin 4 // (gate r).finish w = none} where
  toFun i := ⟨i.natAdd 2, by
    change gateFinish (i.natAdd 2) = none
    simp [gateFinish]⟩
  invFun w := ⟨w.val.val - 2, by have hw := w.val.isLt; omega⟩
  left_inv i := by apply Fin.ext; change 2 + i.val - 2 = i.val; omega
  right_inv w := by
    apply Subtype.ext
    apply Fin.ext
    have hw := w.property
    change gateFinish w.val = none at hw
    have bound : 2 ≤ w.val.val := by
      unfold gateFinish at hw
      split at hw
      · cases hw
      · omega
    change 2 + (w.val.val - 2) = w.val.val
    omega

private def drawnCrossing (r : Bool) :
    IsolatedRuntimeGenerator (gateEdge r) (crossCap (!r)) (crossCap r) where
  drawing :=
    { vertices := 1
      wires := 4
      drawing := gate r
      input := (finCongr (crossSize (!r))).trans (lowerSlots r)
      output := (finCongr (crossSize r)).trans (upperSlots r)
      input_label i := by cases r <;> change Fin 2 at i <;> fin_cases i <;> rfl
      output_label i := by cases r <;> change Fin 2 at i <;> fin_cases i <;> rfl
      input_x i := by
        cases r <;> change Fin 2 at i <;> fin_cases i
        · change (1 / 6 : ℝ) + 0 / 2 = ActiveStrip.left.place (1 / 3)
          norm_num [ActiveStrip.place]
        · change (2 / 3 : ℝ) - 0 / 2 = ActiveStrip.right.place (1 / 3)
          norm_num [ActiveStrip.place]
        · change (1 / 6 : ℝ) + 0 / 2 = 1 / 6
          norm_num
        · change (2 / 3 : ℝ) - 0 / 2 = 2 / 3
          norm_num
      output_x i := by
        cases r <;> change Fin 2 at i <;> fin_cases i
        · change (2 / 3 : ℝ) - 1 / 2 = 1 / 6
          norm_num
        · change (1 / 6 : ℝ) + 1 / 2 = 2 / 3
          norm_num
        · change (2 / 3 : ℝ) - 1 / 2 = ActiveStrip.left.place (1 / 3)
          norm_num [ActiveStrip.place]
        · change (1 / 6 : ℝ) + 1 / 2 = ActiveStrip.right.place (1 / 3)
          norm_num [ActiveStrip.place] }
  vertex := (0 : Fin 1)
  only _ := Subsingleton.elim (α := Fin 1) _ _
  label := rfl
  noThrough i := by
    change ¬ (gate r).crosses i (1 / 2)
    fin_cases i <;> norm_num [ProgressiveGraph.Diagram.crosses, ProgressiveGraph.Diagram.lower,
      ProgressiveGraph.Diagram.upper, gate, gateStart, gateFinish, endpointHeight, Set.mem_Ioo]

example (e : Bool) :
    let outer : FixedRuntimeCap effects := ⟨outsideCap, [()], rfl⟩
    readout.map (X := outer) (Y := outer) (FixedRuntimeCap.ofDrawing
      ((drawnCrossing true).drawing.thenDo ((placedDrawing e).thenDo (drawnCrossing false).drawing))) =
    (Computations.whiskerLeft (Computations.mk (G := effects) [()])).map (Computations.effect (G := effects) e) := by
  have compared := FixedRuntimeCap.toComputations_leftScalar (G := effects)
    (A := runtimeCap.cap) (B := runtimeCap.cap) (E := outsideCap) (H := outsideCap)
    () idleCap rfl rfl rfl rfl rfl
    (show runtimeCap.cap ⟶ runtimeCap.cap from geometricEffect e)
    (drawnCrossing true) (drawnCrossing false)
  change readout.map (X := ⟨outsideCap, [()], rfl⟩) (Y := ⟨outsideCap, [()], rfl⟩)
    (FixedCap.ofDrawing (a := outsideCap) (b := outsideCap)
      ((drawnCrossing true).drawing.thenDo ((placedDrawing e).thenDo (drawnCrossing false).drawing))) = _
  erw [← FixedCap.comp_drawings (a := outsideCap) (b := innerCap) (c := outsideCap),
    ← FixedCap.comp_drawings (a := innerCap) (b := innerCap) (c := outsideCap),
    ← placedEffect_drawing e]
  exact compared.trans
    (congrArg (Computations.whiskerLeft (Computations.mk (G := effects) [()])).map (read_effect e))

end Silmaril.RuntimeWires.Proofs.RuntimeReadout.Regression
