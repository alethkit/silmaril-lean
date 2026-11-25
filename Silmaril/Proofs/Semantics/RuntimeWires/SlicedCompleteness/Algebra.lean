module

public import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Moves
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Encoding

public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem then_empty {A B : List O} (p : Sheet S A B) : p.thenDo (.empty B) = p :=
  sheet_ext (by simp only [seq_cells, sheetCells, List.append_nil])

theorem then_assoc {A B C D : List O} (p : Sheet S A B) (q : Sheet S B C) (r : Sheet S C D) :
    (p.thenDo q).thenDo r = p.thenDo (q.thenDo r) :=
  sheet_ext (by simp only [seq_cells, List.append_assoc])

theorem tensor_id (A B : List O) :
    (Sheet.empty (S := S) A).tensor (.empty B) = .empty (A ++ B) := rfl

theorem tensor_unit_left {A B : List O} (p : Sheet S A B) :
    ((Sheet.empty []).tensor p).reindex (List.nil_append _) (List.nil_append _) = p := by
  apply sheet_ext
  simp only [Sheet.tensor, sheet_reindex_cells, seq_cells, Sheet.padRight, sheetCells,
    pad_left_cells, List.map_nil, List.nil_append]
  exact List.map_id _

theorem tensor_unit_right {A B : List O} (p : Sheet S A B) :
    (p.tensor (.empty [])).reindex (List.append_nil _) (List.append_nil _) = p := by
  apply sheet_ext
  simp only [Sheet.tensor, sheet_reindex_cells, seq_cells, Sheet.padLeft, sheetCells,
    pad_right_cells, List.map_nil, List.append_nil]
  exact List.map_id _

theorem tensor_assoc {A B X Y U V : List O} (p : Sheet S A B) (q : Sheet S X Y)
    (r : Sheet S U V) :
    ((p.tensor q).tensor r).reindex (List.append_assoc ..) (List.append_assoc ..) =
      p.tensor (q.tensor r) := by
  apply sheet_ext
  simp only [Sheet.tensor, sheet_reindex_cells, seq_cells, pad_left_cells, pad_right_cells,
    List.map_append, List.map_map, Function.comp_def, List.append_assoc]

theorem tensor_comp {A B C X Y Z : List O}
    (f : Sheet S A B) (g : Sheet S B C) (h : Sheet S X Y) (k : Sheet S Y Z) :
    Sheet.SeamEquivalent ((f.thenDo g).tensor (h.thenDo k)) ((f.tensor h).thenDo (g.tensor k)) := by
  let firstPart := f.padRight X
  let lastPart := k.padLeft C
  have h₁ : (f.thenDo g).tensor (h.thenDo k) = (firstPart.thenDo (g.tensor h)).thenDo lastPart := by
    apply sheet_ext
    simp only [firstPart, lastPart, Sheet.tensor, seq_cells, pad_left_cells, pad_right_cells,
      List.map_append, List.append_assoc]
  have h₂ : (f.tensor h).thenDo (g.tensor k) =
      (firstPart.thenDo ((h.padLeft B).thenDo (g.padRight Y))).thenDo lastPart := by
    apply sheet_ext
    simp only [firstPart, lastPart, Sheet.tensor, seq_cells, pad_left_cells, pad_right_cells,
      List.append_assoc]
  rw [h₁, h₂]
  exact seam_then (seam_then (.refl _) (swap_sheets g h)) (.refl _)

theorem encode_reindex {A B X Y : List O} (a : A = X) (b : B = Y) (f : Diagram S A B) :
    Sheet.encode (Diagram.reindex a b f) = (Sheet.encode f).reindex a b := by
  subst a
  subst b
  rfl

private theorem of_eq {A B : List O} {p q : Sheet S A B} (h : p = q) : Sheet.SeamEquivalent p q :=
  h ▸ .refl _

/-- The schedule map respects the free monoidal congruence by independent seam moves. -/
theorem encode_congr {A B : List O} {f g : Diagram S A B}
    (h : Diagram.Congruence (fun {_ _} _ _ => False) f g) :
    Sheet.SeamEquivalent (Sheet.encode f) (Sheet.encode g) := by
  induction h with
  | equation h => exact False.elim h
  | refl => exact .refl _
  | symm _ ih => exact .symm _ _ ih
  | trans _ _ hf hg => exact .trans _ _ _ hf hg
  | comp _ _ hf hg => exact seam_then hf hg
  | tensor _ _ hf hg => exact seam_tensor hf hg
  | id_comp => exact .refl _
  | comp_id f => exact of_eq (then_empty (Sheet.encode f))
  | comp_assoc f g h => exact of_eq (then_assoc (Sheet.encode f) (Sheet.encode g) (Sheet.encode h))
  | tensor_id A B => exact of_eq (tensor_id A B)
  | tensor_comp f g h k => exact tensor_comp (Sheet.encode f) (Sheet.encode g) (Sheet.encode h) (Sheet.encode k)
  | tensor_unit_left f =>
    rw [encode_reindex]
    exact of_eq (tensor_unit_left (Sheet.encode f))
  | tensor_unit_right f =>
    rw [encode_reindex]
    exact of_eq (tensor_unit_right (Sheet.encode f))
  | tensor_assoc f g h =>
    rw [encode_reindex]
    exact of_eq (tensor_assoc (Sheet.encode f) (Sheet.encode g) (Sheet.encode h))

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness
