module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.RuntimeReadout.Thms
import Silmaril.Semantics.RuntimeWires.Presentation.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.RuntimeReadout.Regression

open CategoryTheory Presentation ProgressiveGraph

private abbrev effects : EffectfulPolygraph where
  Obj := PEmpty
  pure := Signature.empty PEmpty
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

private theorem read_effect (e : Bool) : readout.map (geometricEffect e) = Computations.effect e := by
  have noThrough (w : Fin 2) : ¬ (effectDiagram e).crosses w (1 / 2) := by
    fin_cases w <;> norm_num [ProgressiveGraph.Diagram.crosses, ProgressiveGraph.Diagram.lower,
      ProgressiveGraph.Diagram.upper, effectDiagram, start, finish, endpointHeight, Set.mem_Ioo]
  have h := FixedRuntimeCap.map_effect (X := runtimeCap) (Y := runtimeCap) e
    (generatorDrawing e) (0 : Fin 1) (fun _ => Subsingleton.elim (α := Fin 1) _ _) rfl noThrough rfl rfl
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
  | _, _, .gen (Edge.moveLeft x) => x.elim
  | _, _, .gen (Edge.moveRight x) => x.elim
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
    | moveLeft x => exact x.elim
    | moveRight x => exact x.elim
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
    | cancelRight x => exact x.elim
    | cancelLeft x => exact x.elim
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

end Silmaril.RuntimeWires.Proofs.RuntimeReadout.Regression
