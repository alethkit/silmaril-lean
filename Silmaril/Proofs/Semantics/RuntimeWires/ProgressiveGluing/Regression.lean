module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Thms
public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing.Regression

open ProgressiveGraph Sliced

private abbrev signature : Signature Unit where
  Edge := Bool
  source e := if e then [()] else []
  target e := if e then [] else [()]

private noncomputable def height (_ : Fin 1) : ℝ := 1 / 2
private noncomputable def sourceX (_ : Fin 1) : ℝ := 1 / 4
private noncomputable def sinkX (_ : Fin 1) : ℝ := 1 / 2

private noncomputable def rising : Wire (height 0) 1 where
  x y := y / 2
  increasing := by norm_num [height]
  continuous := continuous_id.continuousOn.div_const 2
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    ring

private noncomputable def vertical : Wire 0 (height 0) where
  x _ := 1 / 2
  increasing := by norm_num [height]
  continuous := continuousOn_const
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    ring

/-- A source emits a strand that approaches the cap diagonally. -/
private noncomputable def source : ProgressiveGraph.Diagram signature 1 1 .point where
  vertexX := sourceX
  vertexHeight := height
  vertex_inside := by intro v; norm_num [sourceX, height, Set.mem_Ioo]
  vertex_separation := fun {_ _} _ => Subsingleton.elim _ _
  generator := fun _ => false
  label := fun _ => ()
  start := fun _ => some 0
  finish := fun _ => none
  wire := fun _ => rising
  wire_inside w y h := by
    rcases h with ⟨lo, hi⟩
    change (1 : ℝ) / 2 ≤ y at lo
    change y ≤ 1 at hi
    change 0 < y / 2 ∧ y / 2 < 1
    constructor <;> linarith
  start_attached := by intro w v eq; norm_num [rising, height, sourceX]
  finish_attached := by simp
  separated := fun different => (different (Subsingleton.elim _ _)).elim
  avoids_vertex := by intro w v h; simp [endpointHeight, height, Set.mem_Ioo] at h
  input_boundary_separated := fun different => (different (Subsingleton.elim _ _)).elim
  output_boundary_separated := fun different => (different (Subsingleton.elim _ _)).elim
  input := fun _ i => Fin.elim0 i
  output := fun _ _ => 0
  input_exact := by simp [signature]
  output_exact := by
    intro v w
    have hv : v = 0 := Subsingleton.elim ..
    have hw : w = 0 := Subsingleton.elim ..
    subst v
    subst w
    exact ⟨fun _ => ⟨(0 : Fin 1), rfl⟩, fun _ => rfl⟩
  input_types := by simp [List.ofFn_zero]
  output_types := by simp [List.ofFn_succ]
  input_order := fun _ {i} => Fin.elim0 i
  output_order := by
    intro v i j lt
    have eq := @Subsingleton.elim (Fin 1) inferInstance i j
    exact (lt.ne eq).elim

/-- A sink receives a vertical strand from the same cap coordinate. -/
private noncomputable def sink : ProgressiveGraph.Diagram signature 1 1 .point where
  vertexX := sinkX
  vertexHeight := height
  vertex_inside := by intro v; norm_num [sinkX, height, Set.mem_Ioo]
  vertex_separation := fun {_ _} _ => Subsingleton.elim _ _
  generator := fun _ => true
  label := fun _ => ()
  start := fun _ => none
  finish := fun _ => some 0
  wire := fun _ => vertical
  wire_inside := by intros; norm_num [vertical, Set.mem_Ioo]
  start_attached := by simp
  finish_attached := by intro w v eq; rfl
  separated := fun different => (different (Subsingleton.elim _ _)).elim
  avoids_vertex := by intro w v h; simp [endpointHeight, height, Set.mem_Ioo] at h
  input_boundary_separated := fun different => (different (Subsingleton.elim _ _)).elim
  output_boundary_separated := fun different => (different (Subsingleton.elim _ _)).elim
  input := fun _ _ => 0
  output := fun _ i => Fin.elim0 i
  input_exact := by
    intro v w
    have hv : v = 0 := Subsingleton.elim ..
    have hw : w = 0 := Subsingleton.elim ..
    subst v
    subst w
    exact ⟨fun _ => ⟨(0 : Fin 1), rfl⟩, fun _ => rfl⟩
  output_exact := by simp [signature]
  input_types := by simp [List.ofFn_succ]
  output_types := by simp [List.ofFn_zero]
  input_order := by
    intro v i j lt
    have eq := @Subsingleton.elim (Fin 1) inferInstance i j
    exact (lt.ne eq).elim
  output_order := fun _ {i} => Fin.elim0 i

private theorem aligned : source.VerticalMatch sink where
  lower_cap _ := rfl
  upper_cap _ := rfl
  label _ := rfl
  coordinate _ := by
    change (1 : ℝ) / 2 = 1 / 2
    rfl

/-- The joined strand bends at the cut. Its middle point differs from the
chord between the three indicated heights. -/
example : aligned.glue.x 0 (1 / 2) ≠
    (aligned.glue.x 0 (1 / 4) + aligned.glue.x 0 (3 / 4)) / 2 := by
  have first := aligned.glue_x_below 0 (y := 1 / 4) (by norm_num)
  have middle := aligned.glue_x_below 0 (y := 1 / 2) le_rfl
  have last := aligned.glue_x_above 0 (y := 3 / 4) (by norm_num)
  rw [first, middle, last]
  change slabHeight 0 (1 / 2) / 2 ≠ (slabHeight 0 (1 / 4) / 2 + 1 / 2) / 2
  norm_num [slabHeight]

example : aligned.glue.Regular (1 / 2) ∧ aligned.glue.crosses 0 (1 / 2) :=
  ⟨aligned.join_regular, aligned.crosses_join 0⟩

private theorem sourceIsolated : source.Isolates 0 (1 / 4) (3 / 4) :=
  ⟨by norm_num, by norm_num [source, height], by norm_num [source, height], by norm_num,
    fun v _ => Subsingleton.elim v 0⟩

private theorem sinkIsolated : sink.Isolates 0 (1 / 4) (3 / 4) :=
  ⟨by norm_num, by norm_num [sink, height], by norm_num [sink, height], by norm_num,
    fun v _ => Subsingleton.elim v 0⟩

private noncomputable def sourceEvent := Classical.choice (source.single_event sourceIsolated)
private noncomputable def sinkEvent := Classical.choice (sink.single_event sinkIsolated)

/-- Independently slice both vertices of the glued drawing at its actual join. -/
private noncomputable def gluedRead :
    aligned.glue.TwoEventSlice (Fin.castAdd 1 (0 : Fin 1)) (Fin.natAdd 1 (0 : Fin 1))
      (halfHeight 0 (1 / 4)) (1 / 2) (halfHeight 1 (3 / 4)) :=
  ⟨Classical.choice (aligned.glue.single_event (aligned.isolates_lower sourceIsolated)),
   Classical.choice (aligned.glue.single_event (aligned.isolates_upper sinkIsolated))⟩

example : gluedRead.firstEvent.afterWires = [0] ∧ gluedRead.secondEvent.beforeWires = [0] := by
  have seam : aligned.glue.OrderedCut (1 / 2) [0] :=
    ⟨fun w => ⟨fun _ => aligned.crosses_join w, fun _ => List.mem_singleton.mpr (Subsingleton.elim w 0)⟩,
      List.pairwise_singleton _ _⟩
  exact ⟨ProgressiveGraph.Diagram.ordered_cut_unique gluedRead.firstEvent.after seam,
    ProgressiveGraph.Diagram.ordered_cut_unique gluedRead.secondEvent.before seam⟩

example :
    ∃ (first : gluedRead.firstEvent.beforeWires.map aligned.glue.label = sourceEvent.beforeWires.map source.label)
      (last : gluedRead.secondEvent.afterWires.map aligned.glue.label = sinkEvent.afterWires.map sink.label)
      (join : sinkEvent.beforeWires.map sink.label = sourceEvent.afterWires.map source.label),
      gluedRead.sheet.reindex first last =
        (Sheet.cons sourceEvent.cutRow (.empty _)).thenDo
          ((Sheet.cons sinkEvent.cutRow (.empty _)).reindex join rfl) :=
  aligned.concat_readback sourceEvent sinkEvent sourceIsolated sinkIsolated gluedRead

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing.Regression
