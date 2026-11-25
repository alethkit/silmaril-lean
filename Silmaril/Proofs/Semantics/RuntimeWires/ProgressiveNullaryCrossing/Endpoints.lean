module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveNullaryCrossing.Partitions

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable {d : Diagram S V W .point} {moved other : Fin V} {s : d.NullarySlide moved}
variable {side : NullarySlide.Side} (c : s.Crossing other side)
variable (p : c.tied.PairSlice (side.leftVertex moved other) (side.rightVertex moved other) c.lowerCut c.upperCut)

def scalarEvent {h lo hi : ℝ} (valid : h ∈ Set.Icc s.bottom s.top) (ports : List (Fin W))
    (atEvent : c.tied.OrderedCut h (scalarLeft c p ports ++ scalarRight c p ports))
    (attached : ∀ w ∈ ports, c.tied.x w (d.vertexHeight other) = d.vertexX other)
    (before : c.tied.OrderedCut lo (scalarLeft c p ports ++ scalarRight c p ports))
    (after : c.tied.OrderedCut hi (scalarLeft c p ports ++ scalarRight c p ports)) :
    (s.atHeight h valid).EventSlice moved lo hi where
  left := scalarLeft c p ports
  right := scalarRight c p ports
  left_exact w := by
    rw [s.moved_height valid, active_eq c valid]
    exact (scalar_partition c p valid atEvent attached w).1
  right_exact w := by
    rw [s.moved_height valid, active_eq c valid]
    exact (scalar_partition c p valid atEvent attached w).2
  before := (cut_transport c valid).mpr (by simpa only [no_inputs valid, List.append_nil] using before)
  after := (cut_transport c valid).mpr (by simpa only [no_outputs valid, List.append_nil] using after)

def stationaryEvent {h lo hi : ℝ} (valid : h ∈ Set.Icc s.bottom s.top)
    (before : c.tied.OrderedCut lo p.inputWires)
    (after : c.tied.OrderedCut hi p.outputWires) :
    (s.atHeight h valid).EventSlice other lo hi where
  left := stationaryLeft c p
  right := stationaryRight c p
  left_exact w := by
    rw [height_other c valid, active_eq c valid]
    exact (stationary_partition c p w).1
  right_exact w := by
    rw [height_other c valid, active_eq c valid]
    exact (stationary_partition c p w).2
  before := (cut_transport c valid).mpr (by
    change c.tied.OrderedCut lo ((stationaryLeft c p ++ c.tied.inputs other) ++ stationaryRight c p)
    rwa [← stationary_input_form c p])
  after := (cut_transport c valid).mpr (by
    change c.tied.OrderedCut hi ((stationaryLeft c p ++ c.tied.outputs other) ++ stationaryRight c p)
    rwa [← stationary_output_form c p])

theorem early_cut : c.tied.OrderedCut c.earlyCut p.inputWires :=
  cut_before c p.before (c.lower_bottom.trans c.bottom_early).le c.early_other

theorem late_cut : c.tied.OrderedCut c.lateCut p.outputWires :=
  cut_after c p.after c.other_late (c.late_top.trans c.top_upper).le

def lowerEndpoint : s.initial.TwoEventSlice moved other c.lowerCut c.earlyCut c.upperCut where
  firstEvent := scalarEvent c p ⟨le_rfl, s.ordered.le⟩ (c.tied.inputs other)
    (by rw [← input_form c p]; exact cut_before c p.before c.lower_bottom.le (c.bottom_early.trans c.early_other))
    (fun _ => incoming_attached c)
    (by rw [← input_form c p]; exact p.before)
    (by rw [← input_form c p]; exact early_cut c p)
  secondEvent := stationaryEvent c p ⟨le_rfl, s.ordered.le⟩ (early_cut c p) p.after

def upperEndpoint : s.terminal.TwoEventSlice other moved c.lowerCut c.lateCut c.upperCut where
  firstEvent := stationaryEvent c p ⟨s.ordered.le, le_rfl⟩ p.before (late_cut c p)
  secondEvent := scalarEvent c p ⟨s.ordered.le, le_rfl⟩ (c.tied.outputs other)
    (by rw [← output_form c p]; exact cut_after c p.after (c.other_late.trans c.late_top) c.top_upper.le)
    (fun _ => outgoing_attached c)
    (by rw [← output_form c p]; exact late_cut c p)
    (by rw [← output_form c p]; exact p.after)

/-- Any two geometric reads of a single event at these cuts have the same
ordered passing blocks. -/
theorem event_unique {g : Diagram S V W .point} {j : Fin V} {lo hi : ℝ}
    (a b : g.EventSlice j lo hi) : a = b := by
  have sorted (l r : List (Fin W)) (hl : l.Pairwise (fun x y => g.x x lo < g.x y lo))
      (hr : r.Pairwise (fun x y => g.x x lo < g.x y lo)) (mem : ∀ w, w ∈ l ↔ w ∈ r) : l = r := by
    have nodup (as : List (Fin W)) (p : as.Pairwise (fun x y => g.x x lo < g.x y lo)) : as.Nodup :=
      p.imp (fun lt => ne_of_apply_ne (fun w => g.x w lo) (ne_of_lt lt))
    exact ((List.perm_ext_iff_of_nodup (nodup l hl) (nodup r hr)).mpr mem).eq_of_pairwise
      (fun _ _ _ _ hab hba => (lt_asymm hab hba).elim) hl hr
  have left (e : g.EventSlice j lo hi) : e.left.Pairwise (fun x y => g.x x lo < g.x y lo) :=
    (List.pairwise_append.mp (List.pairwise_append.mp e.before.ordered).1).1
  have right (e : g.EventSlice j lo hi) : e.right.Pairwise (fun x y => g.x x lo < g.x y lo) :=
    (List.pairwise_append.mp e.before.ordered).2.1
  have lhs := sorted a.left b.left (left a) (left b) (fun w => (a.left_exact w).trans (b.left_exact w).symm)
  have rhs := sorted a.right b.right (right a) (right b) (fun w => (a.right_exact w).trans (b.right_exact w).symm)
  cases a
  cases b
  cases lhs
  cases rhs
  rfl

theorem endpoint_unique {g : Diagram S V W .point} {i j : Fin V} {lo mid hi : ℝ}
    (a b : g.TwoEventSlice i j lo mid hi) : a = b := by
  cases a with
  | mk a₁ a₂ =>
    cases b with
    | mk b₁ b₂ =>
      cases event_unique a₁ b₁
      cases event_unique a₂ b₂
      rfl

end Silmaril.RuntimeWires.Proofs.ProgressiveNullaryCrossing
