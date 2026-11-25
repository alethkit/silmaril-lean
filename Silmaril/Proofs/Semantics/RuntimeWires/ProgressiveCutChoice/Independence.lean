module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSweep.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveCutChoice

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {d : Diagram S V W}

theorem relocate {i : Fin (V + 1)} {h k : ℝ} (hh : h ∈ d.gap i) (hk : k ∈ d.gap i)
    {wires : List (Fin W)} (cut : d.OrderedCut h wires) : d.OrderedCut k wires := by
  have same_active (w : Fin W) {y : ℝ} (hy : y ∈ d.gap i) :
      d.crosses w h ↔ d.crosses w y :=
    (Diagram.gap_crosses_iff_indices hh w).trans (Diagram.gap_crosses_iff_indices hy w).symm
  refine ⟨fun w => (cut.exact_wires w).trans (same_active w hk), cut.ordered.imp_of_mem ?_⟩
  intro a b ha hb hab
  have hne : a ≠ b := ne_of_apply_ne (fun w => d.x w h) (ne_of_lt hab)
  have active (y : ℝ) (hy : y ∈ Set.uIcc h k) :
      d.crosses a y ∧ d.crosses b y := by
    have hg : y ∈ d.gap i :=
      ⟨(lt_min hh.1 hk.1).trans_le hy.1, hy.2.trans_lt (max_lt hh.2 hk.2)⟩
    exact ⟨(same_active a hg).mp ((cut.exact_wires a).mp ha),
      (same_active b hg).mp ((cut.exact_wires b).mp hb)⟩
  have covers (y : ℝ) (hy : y ∈ Set.uIcc h k) : d.covers a y ∧ d.covers b y := by
    obtain ⟨x, z⟩ := active y hy
    exact ⟨⟨x.1.le, x.2.le⟩, ⟨z.1.le, z.2.le⟩⟩
  exact Diagram.order_across covers (fun y hy => d.separated hne (active y hy).1 (covers y hy).2) hab

theorem wires_eq (s t : d.Sweep) (i : Fin (V + 1)) : s.wires i = t.wires i :=
  Diagram.ordered_cut_unique (relocate (s.cuts.in_gap i) (t.cuts.in_gap i) (s.ordered i)) (t.ordered i)

private theorem left_nodup {v : Fin V} {lo hi : ℝ} (e : d.EventSlice v lo hi) : e.left.Nodup :=
  ((List.pairwise_append.mp (List.pairwise_append.mp e.before.ordered).1).1).imp
    (fun hlt => ne_of_apply_ne (fun w => d.x w lo) (ne_of_lt hlt))

private theorem event_blocks {v : Fin V} {lo hi lo' hi' : ℝ}
    (e : d.EventSlice v lo hi) (f : d.EventSlice v lo' hi')
    (same : e.beforeWires = f.beforeWires) : e.left = f.left ∧ e.right = f.right := by
  have perm := (List.perm_ext_iff_of_nodup (left_nodup e) (left_nodup f)).mpr
    (fun w => (e.left_exact w).trans (f.left_exact w).symm)
  change e.left ++ d.inputs v ++ e.right = f.left ++ d.inputs v ++ f.right at same
  simp only [List.append_assoc] at same
  obtain ⟨left, rest⟩ := List.append_inj same perm.length_eq
  exact ⟨left, List.append_inj_right rest rfl⟩

private theorem one_box_heq (e : S.Edge) {left left' right right' : List O}
    (hl : left = left') (hr : right = right') :
    HEq (Sliced.Row.pass left (Sliced.Row.box e (Sliced.Row.straight right)))
      (Sliced.Row.pass left' (Sliced.Row.box e (Sliced.Row.straight right'))) := by
  subst left'
  subst right'
  rfl

private theorem row_to_event (s : d.Sweep) (i : Fin V) :
    HEq (s.row i) (s.event i).row := by
  have toCut : HEq (s.row i) (s.event i).cutRow := by
    unfold Diagram.Sweep.row
    exact cast_heq _ _
  have toEvent : HEq (s.event i).cutRow (s.event i).row := by
    unfold Diagram.EventSlice.cutRow
    exact cast_heq _ _
  exact toCut.trans toEvent

private theorem row_heq (s t : d.Sweep) (i : Fin V) : HEq (s.row i) (t.row i) := by
  have before := (s.before i).trans ((wires_eq s t i.castSucc).trans (t.before i).symm)
  obtain ⟨left, right⟩ := event_blocks (s.event i) (t.event i) before
  have raw : HEq (s.event i).row (t.event i).row :=
    one_box_heq (d.generator (d.vertexOrder i)) (congrArg (List.map d.label) left)
      (congrArg (List.map d.label) right)
  exact (row_to_event s i).trans (raw.trans (row_to_event t i).symm)

private theorem joinRows_eq {n : ℕ} {a b : Fin (n + 1) → List O} (words : a = b)
    (r : ∀ i : Fin n, Sliced.Row S (a i.castSucc) (a i.succ))
    (q : ∀ i : Fin n, Sliced.Row S (b i.castSucc) (b i.succ))
    (rows : ∀ i, HEq (r i) (q i)) :
    (congrArg₂ (Sliced.Sheet S) (congrFun words 0) (congrFun words (Fin.last n))).mp
      (Diagram.Sweep.joinRows a r) = Diagram.Sweep.joinRows b q := by
  subst b
  have eq : r = q := funext (fun i => eq_of_heq (rows i))
  subst q
  rfl

theorem sheet_eq (s t : d.Sweep) :
    (congrArg₂ (Sliced.Sheet S)
      (congrArg (List.map d.label) (wires_eq s t 0))
      (congrArg (List.map d.label) (wires_eq s t (Fin.last V)))).mp s.sheet = t.sheet := by
  have words : (fun i => (s.wires i).map d.label) = (fun i => (t.wires i).map d.label) :=
    funext (fun i => congrArg (List.map d.label) (wires_eq s t i))
  exact joinRows_eq words s.row t.row (row_heq s t)

end Silmaril.RuntimeWires.Proofs.ProgressiveCutChoice
