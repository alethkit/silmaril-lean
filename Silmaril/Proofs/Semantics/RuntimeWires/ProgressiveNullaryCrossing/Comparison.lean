module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Endpoints
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing

open ProgressiveGraph ProgressiveGraph.Diagram Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : ProgressiveGraph.Diagram S V W .point} {moved other : Fin V} {s : d.NullarySlide moved}
variable {side : NullarySlide.Side} (c : s.Crossing other side)
variable (p : c.tied.PairSlice (side.leftVertex moved other) (side.rightVertex moved other) c.lowerCut c.upperCut)

def assemble (early : s.initial.TwoEventSlice moved other c.lowerCut c.earlyCut c.upperCut)
    (late : s.terminal.TwoEventSlice other moved c.lowerCut c.lateCut c.upperCut) : c.Readback where
  tie := p
  early := early
  late := late
  early_input := ordered_cut_unique early.firstEvent.before
    ((cut_transport c ⟨le_rfl, s.ordered.le⟩).mpr p.before)
  early_output := ordered_cut_unique early.secondEvent.after
    ((cut_transport c ⟨le_rfl, s.ordered.le⟩).mpr p.after)
  late_input := ordered_cut_unique late.firstEvent.before
    ((cut_transport c ⟨s.ordered.le, le_rfl⟩).mpr p.before)
  late_output := ordered_cut_unique late.secondEvent.after
    ((cut_transport c ⟨s.ordered.le, le_rfl⟩).mpr p.after)

def readings : c.Readback := assemble c p (lowerEndpoint c p) (upperEndpoint c p)

theorem exists_readback : Nonempty c.Readback := by
  obtain ⟨tied⟩ := simultaneous_event (tied_pair c)
  obtain ⟨firstEarly⟩ := single_event (early_first c)
  obtain ⟨secondEarly⟩ := single_event (early_second c)
  obtain ⟨firstLate⟩ := single_event (late_first c)
  obtain ⟨secondLate⟩ := single_event (late_second c)
  exact ⟨assemble c tied ⟨firstEarly, secondEarly⟩ ⟨firstLate, secondLate⟩⟩

private theorem event_cells {g : ProgressiveGraph.Diagram S V W .point} {j : Fin V} {lo hi : ℝ}
    (e : g.EventSlice j lo hi) :
    e.row.cells = (e.left.map g.label).map Sum.inl ++
      (Sum.inr (g.generator j) :: (e.right.map g.label).map Sum.inl) := by
  simp only [EventSlice.row, Row.cells_pass, Row.cells_box, Row.cells_straight]

private theorem two_cells {g : ProgressiveGraph.Diagram S V W .point} {i j : Fin V} {lo mid hi : ℝ}
    (r : g.TwoEventSlice i j lo mid hi) :
    r.sheet.cells = [r.firstEvent.row.cells, r.secondEvent.row.cells] := by
  simp only [TwoEventSlice.sheet, Sheet.cells_empty, Sheet.cells_reindex, Sheet.cells_cons]

private theorem left_first_cells {g : ProgressiveGraph.Diagram S V W .point}
    {l r : Fin V} {lo hi : ℝ} (q : g.PairSlice l r lo hi) :
    q.leftFirst.cells =
      [(q.left.map g.label).map Sum.inl ++
        (Sum.inr (g.generator l) :: (q.middle.map g.label).map Sum.inl ++
          (S.source (g.generator r)).map Sum.inl ++ (q.right.map g.label).map Sum.inl),
       (q.left.map g.label).map Sum.inl ++ (S.target (g.generator l)).map Sum.inl ++
         (q.middle.map g.label).map Sum.inl ++
           (Sum.inr (g.generator r) :: (q.right.map g.label).map Sum.inl)] := by
  erw [PairSlice.leftFirst, Sheet.cells_cons, Sheet.cells_cons, Sheet.cells_empty,
    Row.cells_beside q.leftRow]
  simp only [PairSlice.leftRow, PairSlice.rightRow, Row.cells_pass, Row.cells_box,
    Row.cells_straight, List.map_append, List.append_assoc, List.cons_append]

private theorem right_first_cells {g : ProgressiveGraph.Diagram S V W .point}
    {l r : Fin V} {lo hi : ℝ} (q : g.PairSlice l r lo hi) :
    q.rightFirst.cells =
      [(q.left.map g.label).map Sum.inl ++ (S.source (g.generator l)).map Sum.inl ++
         (q.middle.map g.label).map Sum.inl ++
           (Sum.inr (g.generator r) :: (q.right.map g.label).map Sum.inl),
       (q.left.map g.label).map Sum.inl ++
         (Sum.inr (g.generator l) :: (q.middle.map g.label).map Sum.inl ++
           (S.target (g.generator r)).map Sum.inl ++ (q.right.map g.label).map Sum.inl)] := by
  erw [PairSlice.rightFirst, Sheet.cells_cons, Sheet.cells_cons, Sheet.cells_empty,
    Row.cells_pass _ q.rightRow]
  simp only [PairSlice.leftRow, PairSlice.rightRow, Row.cells_pass, Row.cells_box,
    Row.cells_straight, Row.cells_beside, List.map_append, List.append_assoc, List.cons_append]

private def schedule {A B : List O} (side : NullarySlide.Side) (left right : Sheet S A B) : Sheet S A B :=
  match side with
  | .left => left
  | .right => right

private theorem early_serial :
    (readings c p).earlySheet = schedule side p.leftFirst p.rightFirst := by
  apply Sheet.cells_injective
  have input : (c.tied.inputs other).map d.label = S.source (d.generator other) :=
    c.tied.input_types other
  have initLabel : s.initial.label = d.label := rfl
  have initGen : s.initial.generator = d.generator := rfl
  have tieLabel : c.tied.label = d.label := rfl
  have tieGen : c.tied.generator = d.generator := rfl
  erw [NullarySlide.Crossing.Readback.earlySheet, Sheet.cells_reindex, two_cells, event_cells, event_cells]
  cases side
  case' left =>
    change _ = p.leftFirst.cells
    rw [left_first_cells p]
  case' right =>
    change _ = p.rightFirst.cells
    rw [right_first_cells p]
  all_goals
    simp only [readings, assemble, lowerEndpoint, scalarEvent, stationaryEvent, scalarLeft, scalarRight,
      stationaryLeft, stationaryRight, initLabel, initGen, tieLabel, tieGen, NullarySlide.Side.leftVertex,
      NullarySlide.Side.rightVertex, List.map_append, List.append_assoc, input, s.no_outputs, List.nil_append,
      List.map_nil, List.cons_append]

private theorem late_serial :
    (readings c p).lateSheet = schedule side p.rightFirst p.leftFirst := by
  apply Sheet.cells_injective
  have output : (c.tied.outputs other).map d.label = S.target (d.generator other) :=
    c.tied.output_types other
  have endLabel : s.terminal.label = d.label := rfl
  have endGen : s.terminal.generator = d.generator := rfl
  have tieLabel : c.tied.label = d.label := rfl
  have tieGen : c.tied.generator = d.generator := rfl
  erw [NullarySlide.Crossing.Readback.lateSheet, Sheet.cells_reindex, two_cells, event_cells, event_cells]
  cases side
  case' left =>
    change _ = p.rightFirst.cells
    rw [right_first_cells p]
  case' right =>
    change _ = p.leftFirst.cells
    rw [left_first_cells p]
  all_goals
    simp only [readings, assemble, upperEndpoint, scalarEvent, stationaryEvent, scalarLeft, scalarRight,
      stationaryLeft, stationaryRight, endLabel, endGen, tieLabel, tieGen, NullarySlide.Side.leftVertex,
      NullarySlide.Side.rightVertex, List.map_append, List.append_assoc, output, s.no_inputs, List.nil_append,
      List.map_nil, List.cons_append]

/-- The two moves from the actual tied sheet to the actual endpoint reads. -/
theorem split_readings :
    Sheet.Move S (readings c p).tiedSheet (readings c p).earlySheet ∧
      Sheet.Move S (readings c p).tiedSheet (readings c p).lateSheet := by
  rw [early_serial c p, late_serial c p]
  have left := Sheet.Move.split (Row.Split.left_first p.leftRow p.rightRow) (.empty _)
  have right := Sheet.Move.split (Row.Split.right_first p.leftRow p.rightRow) (.empty _)
  cases side
  · exact ⟨left, right⟩
  · exact ⟨right, left⟩

theorem compare_readbacks (r : c.Readback) :
    Sheet.Move S r.tiedSheet r.earlySheet ∧ Sheet.Move S r.tiedSheet r.lateSheet := by
  have same : readings c r.tie = r := by
    cases r with
    | mk pair early late beforeEarly afterEarly beforeLate afterLate =>
      change assemble c pair (lowerEndpoint c pair) (upperEndpoint c pair) = _
      cases endpoint_unique (lowerEndpoint c pair) early
      cases endpoint_unique (upperEndpoint c pair) late
      rfl
  rw [← same]
  exact split_readings c r.tie

end Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing
