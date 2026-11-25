module

public import Silmaril.Semantics.RuntimeWires.SerialTrace.Thms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous.LayerRegression

open Silmaril.RuntimeWires.ProgressiveGraph

private abbrev signature : Signature Bool where
  Edge := Fin 4
  source j := if j = 3 then [true] else []
  target j := if j = 2 then [true] else []

private noncomputable def vertexX (j : Fin 4) : ℝ :=
  if j = 0 then 3 / 8 else if j = 1 then 1 / 4 else if j = 2 then 3 / 4 else 27 / 32

private noncomputable def height (j : Fin 4) : ℝ := if j = 3 then 7 / 8 else 1 / 2

private def start (w : Fin 2) : Option (Fin 4) := if w = 0 then none else some 2

private def finish (w : Fin 2) : Option (Fin 4) := if w = 0 then none else some 3

private noncomputable def x (w : Fin 2) (y : ℝ) : ℝ :=
  if w = 0 then (3 + y) / 8 else (5 + 2 * y) / 8

private noncomputable def strand (w : Fin 2) :
    Wire (endpointHeight height 0 (start w)) (endpointHeight height 1 (finish w)) where
  x := x w
  increasing := by fin_cases w <;> norm_num [start, finish, height, endpointHeight]
  continuous := by
    unfold x
    split <;> exact (by fun_prop : Continuous _).continuousOn
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    unfold x
    split <;> ring

/-- Two adjacent scalars lie to the left of a passing wire. The third
vertex creates a slanted wire to a fourth vertex at a later level. -/
private noncomputable def drawing : Diagram signature 4 2 .point where
  vertexX := vertexX
  vertexHeight := height
  vertex_inside := by intro j; fin_cases j <;> norm_num [vertexX, height, Set.mem_Ioo]
  vertex_separation := by
    intro i j he
    have hx := congrArg Prod.fst he
    fin_cases i <;> fin_cases j <;> norm_num [vertexX] at *
  generator := id
  label := fun i => decide (i = 1)
  start := start
  finish := finish
  wire := strand
  wire_inside := by
    intro w y hy
    fin_cases w <;> norm_num [strand, x, start, finish, height, endpointHeight,
      Set.mem_Icc, Set.mem_Ioo] at * <;>
      constructor <;> linarith [hy.1, hy.2]
  start_attached := by
    intro w j he
    fin_cases w <;> fin_cases j <;> norm_num [start, height, vertexX, strand, x] at *
  finish_attached := by
    intro w j he
    fin_cases w <;> fin_cases j <;> norm_num [finish, height, vertexX, strand, x] at *
  separated := by
    intro w z hw y ha hb
    fin_cases w <;> fin_cases z
    all_goals norm_num [strand, x, start, finish, height, endpointHeight, Set.mem_Icc, Set.mem_Ioo] at *
    all_goals
      intro he
      linarith [ha.1, ha.2, hb.1, hb.2]
  avoids_vertex := by
    intro w j hw
    fin_cases w <;> fin_cases j <;>
      norm_num [strand, x, vertexX, height, start, finish, endpointHeight, Set.mem_Ioo] at *
  input_boundary_separated := by
    intro w z hw hs ht
    fin_cases w <;> fin_cases z <;> norm_num [start, strand, x] at *
  output_boundary_separated := by
    intro w z hw hs ht
    fin_cases w <;> fin_cases z <;> norm_num [finish, strand, x] at *
  input _ _ := 1
  output _ _ := 1
  input_exact := by
    intro j w
    fin_cases j <;> fin_cases w <;> simp [signature, finish]
  output_exact := by
    intro j w
    fin_cases j <;> fin_cases w <;> simp [signature, start]
  input_types := by intro j; fin_cases j <;> simp [List.ofFn_succ]
  output_types := by intro j; fin_cases j <;> simp [List.ofFn_succ]
  input_order := by
    intro j i k hij
    have small : (signature.source (id j)).length ≤ 1 := by fin_cases j <;> decide
    omega
  output_order := by
    intro j i k hij
    have small : (signature.target (id j)).length ≤ 1 := by fin_cases j <;> decide
    omega

private theorem layer : drawing.IsolatesLayer (1 / 2) (1 / 4) (3 / 4) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by
    intro j hj
    fin_cases j <;> norm_num [drawing, height, Set.mem_Icc] at *⟩

private noncomputable def slice := Classical.choice (Diagram.layer_slice layer)

private abbrev expected : List (Diagram.LayerSlot 4 2) :=
  [.inr 1, .inr 0, .inl 0, .inr 2]

private theorem expected_exact (c : Diagram.LayerSlot 4 2) :
    c ∈ expected ↔ drawing.atLayer (1 / 2) c := by
  cases c with
  | inl w =>
    fin_cases w <;>
      norm_num [expected, drawing, Diagram.atLayer, Diagram.crosses, Diagram.lower,
        Diagram.upper, endpointHeight, height, start, finish, Set.mem_Ioo]
  | inr j => fin_cases j <;> norm_num [expected, Diagram.atLayer, drawing, height]

private theorem expected_order :
    expected.Pairwise (fun a b => drawing.slotX (1 / 2) a < drawing.slotX (1 / 2) b) := by
  have point (w : Fin 2) (y : ℝ) : (drawing.wire w).x y = x w y := rfl
  simp only [expected, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq]
  norm_num [Diagram.slotX, Diagram.x, point, drawing, vertexX, x]

/-- The two nullary cells are consecutive in the actual geometrically
sorted slot list, despite having no incident wire IDs. -/
private theorem slots_at_half {y lo hi : ℝ} (s : drawing.LayerSlice y lo hi)
    (hy : y = 1 / 2) : s.slots = expected := by
  subst y
  have nd : s.slots.Nodup := s.ordered.imp
    (fun h => ne_of_apply_ne (drawing.slotX (1 / 2)) (ne_of_lt h))
  have perm := (List.perm_ext_iff_of_nodup nd (by simp [expected])).mpr
    (fun c => (s.exact_slots c).trans (expected_exact c).symm)
  exact perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim)
    s.ordered expected_order

private theorem slots : slice.slots = expected := slots_at_half slice rfl

private theorem vertices : slice.vertices = [1, 0, 2] := by
  rw [Diagram.LayerSlice.vertices, slots]
  rfl

example : drawing.OrderedCut (1 / 4) [0] ∧ drawing.OrderedCut (3 / 4) [0, 1] := by
  have h := slice.before
  have k := slice.after
  rw [slots] at h k
  exact ⟨h, k⟩

/-- The ordered typed row reads all three generators, including the two
that produce no contribution to either ordered cut word. -/
example : slice.row.boxCount = 3 := by
  rw [Diagram.LayerSlice.row, slots]
  rfl

noncomputable example : Silmaril.RuntimeWires.Sliced.Row signature [false] [false, true] := by
  have h := slice.cutRow
  rw [slots] at h
  exact h

open Silmaril.RuntimeWires.Sliced

private abbrev order : List (Fin 4) := [2, 0, 1]

private theorem order_perm : order.Perm slice.vertices := by
  rw [vertices]
  exact (List.Perm.swap 0 2 [1]).trans
    ((List.Perm.cons 0 (List.Perm.swap 1 2 [])).trans (List.Perm.swap 1 0 [2]))

private noncomputable def rowGenerators : {A B : List Bool} → Row signature A B → List (Fin 4)
  | _, _, .empty => []
  | _, _, .wire _ tail => rowGenerators tail
  | _, _, .box j tail => j :: rowGenerators tail

private noncomputable def sheetGenerators : {A B : List Bool} → Sheet signature A B → List (List (Fin 4))
  | _, _, .empty _ => []
  | _, _, .cons r tail => rowGenerators r :: sheetGenerators tail

private theorem generators_reindex {A B X Y : List Bool} (a : A = X) (b : B = Y)
    (p : Sheet signature A B) : sheetGenerators (p.reindex a b) = sheetGenerators p := by
  subst a
  subst b
  rfl

/-- The source executes first. The two consecutive scalars execute in
reverse horizontal order, each in its own one-generator row. -/
example : sheetGenerators (slice.serializeCuts order order_perm) = [[2], [0], [1]] := by
  unfold Diagram.LayerSlice.serializeCuts Diagram.LayerSlice.serialize
  rw [generators_reindex, generators_reindex, slots]
  rfl

noncomputable example : Sheet signature [false] [false, true] := by
  have p := slice.serializeCuts order order_perm
  rw [slots] at p
  exact p

example : Sheet.SeamEquivalent (slice.serializeCuts order order_perm) (.cons slice.cutRow (.empty _)) :=
  slice.serializeCuts_seam order order_perm

private theorem levels : drawing.levels = [1 / 2, 7 / 8] := by
  apply (Finset.sortedLT_sort _).eq_of_mem_iff
  · rw [List.sortedLT_iff_pairwise]
    norm_num
  · intro h
    simp [drawing, height, Fin.exists_fin_succ, eq_comm]

private theorem levelCount : drawing.levelCount = 2 := by
  simp [Diagram.levelCount, levels]

private noncomputable def middleCut : Fin (drawing.levelCount + 1) :=
  ⟨1, by rw [levelCount]; decide⟩

private theorem source_level : (drawing.levelIndex 2).val = 0 := by
  change drawing.levels.idxOf (height 2) = 0
  rw [levels]
  norm_num [height]

private theorem sink_level : (drawing.levelIndex 3).val = 1 := by
  change drawing.levels.idxOf (height 3) = 1
  rw [levels]
  have different : (7 / 8 : ℝ) ≠ 1 / 2 := by norm_num
  norm_num [height, List.idxOf_cons_ne _ different]

private theorem caps (s : drawing.LayerSweep) :
    s.wires 0 = [0] ∧ s.wires (Fin.last drawing.levelCount) = [0] := by
  have lower := s.input_order.imp (fun h => ne_of_apply_ne (fun w => drawing.x w 0) (ne_of_lt h))
  have upper := s.output_order.imp (fun h => ne_of_apply_ne (fun w => drawing.x w 1) (ne_of_lt h))
  constructor
  · apply List.perm_singleton.mp ((List.perm_ext_iff_of_nodup lower (by simp)).mpr ?_)
    intro w
    rw [s.input_mem]
    fin_cases w <;> simp [drawing, start]
  · apply List.perm_singleton.mp ((List.perm_ext_iff_of_nodup upper (by simp)).mpr ?_)
    intro w
    rw [s.output_mem]
    fin_cases w <;> simp [drawing, finish]

/-- The through wire meets all three cuts. The transient slanted wire
starts at the tied level and finishes at the second level. -/
private theorem middle_wires (s : drawing.LayerSweep) : s.wires middleCut = [0, 1] := by
  let y := s.cuts.height middleCut
  have inside := (Diagram.level_gap_regular (s.cuts.in_gap middleCut)).inside
  have nd := (s.ordered middleCut).ordered.imp
    (fun h => ne_of_apply_ne (fun w => drawing.x w y) (ne_of_lt h))
  have perm : (s.wires middleCut).Perm [0, 1] := (List.perm_ext_iff_of_nodup nd (by simp)).mpr (by
    intro w
    rw [s.wire_span]
    fin_cases w <;>
      norm_num [middleCut, drawing, Diagram.layerStartIndex, Diagram.layerFinishIndex, start,
        finish, source_level, sink_level]
    change 0 < drawing.levelCount
    rw [levelCount]
    decide)
  apply perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => (lt_asymm h₁ h₂).elim)
    (s.ordered middleCut).ordered
  simp
  change (3 + y) / 8 < (5 + 2 * y) / 8
  linarith [inside.1]

private noncomputable def sweep := drawing.layerSweep

example : sweep.wires 0 = [0] ∧ sweep.wires middleCut = [0, 1] ∧
    sweep.wires (Fin.last drawing.levelCount) = [0] :=
  ⟨(caps sweep).1, middle_wires sweep, (caps sweep).2⟩

noncomputable example : Sheet signature [false] [false] := by
  have a : sweep.word 0 = [false] := by rw [Diagram.LayerSweep.word, (caps sweep).1]; rfl
  have b : sweep.word (Fin.last drawing.levelCount) = [false] := by
    rw [Diagram.LayerSweep.word, (caps sweep).2]; rfl
  exact sweep.sheet.reindex a b

private noncomputable def horizontal (s : drawing.LayerSweep) : s.Schedule :=
  ⟨fun i => (s.layer i).vertices, fun _ => .refl _⟩

private noncomputable def reversed (s : drawing.LayerSweep) : s.Schedule :=
  ⟨fun i => (s.layer i).vertices.reverse, fun i => List.reverse_perm (s.layer i).vertices⟩

private theorem tied_vertices (s : drawing.LayerSweep) :
    (s.layer (drawing.levelIndex 2)).vertices = [1, 0, 2] := by
  have h : drawing.levelHeight (drawing.levelIndex 2) = 1 / 2 :=
    (Diagram.levelHeight_index 2).trans (by norm_num [drawing, height])
  rw [Diagram.LayerSlice.vertices, slots_at_half _ h]
  rfl

example : (reversed sweep).order (drawing.levelIndex 2) = [2, 0, 1] :=
  congrArg List.reverse (tied_vertices sweep)

example : Sheet.SeamEquivalent (sweep.serialSheet (reversed sweep))
    (sweep.serialSheet (horizontal sweep)) :=
  sweep.serial_equiv (reversed sweep) (horizontal sweep)

example (empty : Diagram signature 0 2 .point) : empty.levelCount = 0 := by
  simp [Diagram.levelCount, Diagram.levels]

private theorem sink_vertices (s : drawing.LayerSweep) :
    (s.layer (drawing.levelIndex 3)).vertices = [3] := by
  let e := s.layer (drawing.levelIndex 3)
  have nd := e.vertices_order.imp (fun h => ne_of_apply_ne drawing.vertexX (ne_of_lt h))
  apply List.perm_singleton.mp ((List.perm_ext_iff_of_nodup nd (by simp)).mpr ?_)
  intro v
  rw [e.vertices_exact, Diagram.levelHeight_index]
  fin_cases v <;> norm_num [drawing, height]

private theorem source_name : sweep.namedWire 1 = (true, .box 0 2 0) := by
  have hs : drawing.start 1 = some 2 := rfl
  rw [Diagram.LayerSweep.namedWire, Diagram.LayerSweep.origin, hs]
  change (drawing.label 1, WireOrigin.box (drawing.levelIndex 2).val (sweep.boxOrdinal 2)
    ((drawing.outputs 2).idxOf 1)) = _
  rw [source_level, Diagram.LayerSweep.boxOrdinal, tied_vertices]
  rfl

private theorem cap_name : sweep.namedWire 0 = (false, .boundary 0) := by
  have hs : drawing.start 0 = none := rfl
  rw [Diagram.LayerSweep.namedWire, Diagram.LayerSweep.origin, hs, (caps sweep).1]
  rfl

private abbrev expectedFirst : List (BoxTrace signature) :=
  [⟨1, [], []⟩, ⟨0, [], []⟩, ⟨2, [], [(true, .box 0 2 0)]⟩]

private abbrev expectedSecond : List (BoxTrace signature) :=
  [⟨3, [(true, .box 0 2 0)], []⟩]

private theorem first_trace :
    (sweep.layer (drawing.levelIndex 2)).vertices.map sweep.expectedBox = expectedFirst := by
  rw [tied_vertices]
  change ([⟨1, [], []⟩, ⟨0, [], []⟩, ⟨2, [], [sweep.namedWire 1]⟩] : List (BoxTrace signature)) = _
  rw [source_name]

private theorem second_trace :
    (sweep.layer (drawing.levelIndex 3)).vertices.map sweep.expectedBox = expectedSecond := by
  rw [sink_vertices]
  change ([⟨3, [sweep.namedWire 1], []⟩] : List (BoxTrace signature)) = _
  rw [source_name]

private theorem two_levels {α : Type} (read : Fin drawing.levelCount → α) {first last : α}
    (low : read (drawing.levelIndex 2) = first) (high : read (drawing.levelIndex 3) = last) :
    List.ofFn read = [first, last] := by
  apply List.ext_getElem (by simp [levelCount])
  intro i hi hj
  have bound : i < 2 := by simpa using hj
  have cases_i : i = 0 ∨ i = 1 := by omega
  rcases cases_i with rfl | rfl
  · have eq : (⟨0, by simpa using hi⟩ : Fin drawing.levelCount) = drawing.levelIndex 2 :=
      Fin.ext source_level.symm
    rw [List.getElem_ofFn, eq, low]
    rfl
  · have eq : (⟨1, by simpa using hi⟩ : Fin drawing.levelCount) = drawing.levelIndex 3 :=
      Fin.ext sink_level.symm
    rw [List.getElem_ofFn, eq, high]
    rfl

/-- Both zero-port boxes advance the ordinal before the source. The sink
receives its exact name, and the cap-to-cap wire retains its boundary name. -/
example : sweep.sheet.traceWires =
    ⟨[expectedFirst, expectedSecond], [(false, .boundary 0)]⟩ := by
  rw [sweep.trace_sheet, Diagram.LayerSweep.expectedTrace, (caps sweep).2]
  have rows := two_levels (fun i => (sweep.layer i).vertices.map sweep.expectedBox)
    first_trace second_trace
  rw [rows, List.map_singleton, cap_name]

private theorem reversed_vertices : (reversed sweep).vertices = [2, 0, 1, 3] := by
  have low : (reversed sweep).order (drawing.levelIndex 2) = [2, 0, 1] :=
    congrArg List.reverse (tied_vertices sweep)
  have high : (reversed sweep).order (drawing.levelIndex 3) = [3] :=
    congrArg List.reverse (sink_vertices sweep)
  rw [Diagram.LayerSweep.Schedule.vertices, two_levels _ low high]
  rfl

private theorem serial_source_name : (reversed sweep).namedWire 1 = (true, .box 0 0 0) := by
  have hs : drawing.start 1 = some 2 := rfl
  rw [Diagram.LayerSweep.Schedule.namedWire, Diagram.LayerSweep.Schedule.origin, hs]
  change (drawing.label 1, WireOrigin.box ((reversed sweep).serialRow 2) 0
    ((drawing.outputs 2).idxOf 1)) = _
  rw [Diagram.LayerSweep.Schedule.serialRow, reversed_vertices]
  rfl

private theorem serial_cap_name : (reversed sweep).namedWire 0 = (false, .boundary 0) := by
  have hs : drawing.start 0 = none := rfl
  rw [Diagram.LayerSweep.Schedule.namedWire, Diagram.LayerSweep.Schedule.origin, hs, (caps sweep).1]
  rfl

/-- The source runs before the two scalars and the sink still receives its
wire at the next level. The boundary-to-boundary wire keeps its name. -/
example : (sweep.serialSheet (reversed sweep)).traceWires =
    ⟨[[⟨2, [], [(true, .box 0 0 0)]⟩], [⟨0, [], []⟩], [⟨1, [], []⟩],
      [⟨3, [(true, .box 0 0 0)], []⟩]], [(false, .boundary 0)]⟩ := by
  rw [(reversed sweep).trace_sheet, Diagram.LayerSweep.Schedule.expectedTrace,
    reversed_vertices, (caps sweep).2]
  change (⟨[[⟨2, [], [(reversed sweep).namedWire 1]⟩], [⟨0, [], []⟩], [⟨1, [], []⟩],
    [⟨3, [(reversed sweep).namedWire 1], []⟩]], [(reversed sweep).namedWire 0]⟩ :
    SheetTrace signature) = _
  rw [serial_source_name, serial_cap_name]

example : (reversed sweep).renameOrigin (.box 0 2 0) = some (.box 0 0 0) := by
  have old : sweep.origin 1 = .box 0 2 0 := congrArg Prod.snd source_name
  have new : (reversed sweep).origin 1 = .box 0 0 0 := congrArg Prod.snd serial_source_name
  rw [← old, (reversed sweep).rename_origin, new]

end Silmaril.RuntimeWires.Proofs.ProgressiveSimultaneous.LayerRegression
