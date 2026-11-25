module

public import Silmaril.Formats.Sqlite.TableLeaf.Thms

public section

open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.TableLeaf

namespace Silmaril.Proofs.Formats.Sqlite.TableLeaf.Frame

private theorem beTwo_eq (left right : File.View) (offset : Nat)
    (first : left.get? offset = right.get? offset)
    (second : left.get? (offset + 1) = right.get? (offset + 1)) :
    left.be? offset 2 = right.be? offset 2 := by
  have range : List.range 2 = [0, 1] := rfl
  simp [File.View.be?, range, first, second]

private theorem cell_stop_bound (view : File.View) (offset : Nat) (cell : Cell)
    (accepted : cell? view offset = some cell) : cell.stop ≤ view.length := by
  unfold cell? at accepted
  obtain ⟨⟨size, _⟩, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨⟩, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨key, payloadAt⟩, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨payload, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨⟩, bounded, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  have bounds : payloadAt + size ≤ view.length ∧ offset + 4 ≤ view.length := by
    simpa [guard, failure] using bounded
  have fits : max (payloadAt + size) (offset + 4) ≤ view.length := by omega
  change some ⟨Int64.ofInt (File.signed 8 key.toNat), payload.materialize, offset,
    max (payloadAt + size) (offset + 4)⟩ = some cell at accepted
  cases accepted
  exact fits

private def atSlot (page : File.View) (base content slot : Nat) : Option Cell := do
  let offset ← page.be? (base + 8 + 2 * slot) 2
  guard (content ≤ offset && offset < 512)
  cell? page offset

private theorem mapM_frame {α β : Type} (xs : List α) (left right : α → Option β)
    (results : List β) (accepted : xs.mapM left = some results)
    (same : ∀ a ∈ xs, ∀ b, left a = some b → right a = some b) :
    xs.mapM right = some results := by
  induction xs generalizing results with
  | nil => exact accepted
  | cons x xs ih =>
    cases head : left x with
    | none => simp [List.mapM_cons, head] at accepted
    | some y =>
      cases tail : xs.mapM left with
      | none => simp [List.mapM_cons, head, tail] at accepted
      | some ys =>
        have rightHead := same x (by simp) y head
        have rightTail := ih ys tail (fun a mem => same a (by simp [mem]))
        simpa [List.mapM_cons, head, tail, rightHead, rightTail] using accepted

private theorem atSlot_frame (left right : File.View) (base content slot : Nat)
    (length : left.length = right.length)
    (pointer : left.be? (base + 8 + 2 * slot) 2 = right.be? (base + 8 + 2 * slot) 2)
    (body : ∀ i, content ≤ i → i < left.length → left.get? i = right.get? i)
    (cell : Cell) (accepted : atSlot left base content slot = some cell) :
    atSlot right base content slot = some cell := by
  rw [atSlot, ← pointer]
  unfold atSlot at accepted
  cases entry : left.be? (base + 8 + 2 * slot) 2 with
  | none => simp [entry] at accepted
  | some offset =>
    by_cases inside : content ≤ offset ∧ offset < 512
    · simp [entry, guard, failure, inside] at accepted ⊢
      have fits := cell_stop_bound left offset cell accepted
      exact cell?_frame left right offset cell accepted (length ▸ fits)
        (fun i le lt => body i (Nat.le_trans inside.1 le) (Nat.lt_of_lt_of_le lt fits))
    · simp [entry, guard, failure, inside] at accepted

private theorem read?_gap_frame (left right : File.View) (base count content : Nat) (cells : List Cell)
    (accepted : read? left base = some cells) (length : left.length = right.length)
    (countField : left.be? (base + 3) 2 = some count)
    (contentField : left.be? (base + 5) 2 = some content)
    (headerBytes : ∀ i, base ≤ i → i < base + 8 + 2 * count → left.get? i = right.get? i)
    (body : ∀ i, content ≤ i → i < left.length → left.get? i = right.get? i) :
    read? right base = some cells := by
  have kind := headerBytes base (by omega) (by omega)
  have fragments := headerBytes (base + 7) (by omega) (by omega)
  have sameField (offset : Nat) (above : base ≤ offset) (below : offset + 1 < base + 8 + 2 * count) :
      left.be? offset 2 = right.be? offset 2 :=
    beTwo_eq left right offset (headerBytes offset above (by omega))
      (headerBytes (offset + 1) (by omega) below)
  have free := sameField (base + 1) (by omega) (by omega)
  have rightCount := (sameField (base + 3) (by omega) (by omega)).symm.trans countField
  have rightContent := (sameField (base + 5) (by omega) (by omega)).symm.trans contentField
  have transfer : ∀ cellList, (List.range count).mapM (atSlot left base content) = some cellList →
      (List.range count).mapM (atSlot right base content) = some cellList := by
    intro cellList parsed
    apply mapM_frame _ (atSlot left base content) _ cellList parsed
    intro slot member cell parsed
    have slotBound := List.mem_range.mp member
    have pointer := sameField (base + 8 + 2 * slot) (by omega) (by omega)
    exact atSlot_frame left right base content slot length pointer body cell parsed
  unfold read? at accepted ⊢
  rw [← length, ← kind, ← free, ← fragments, rightCount, rightContent]
  rw [countField, contentField] at accepted
  simp only [← atSlot.eq_def] at accepted ⊢
  obtain ⟨⟨⟩, kindOk, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨⟩, freeOk, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨actualCount, countEq, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  cases countEq
  obtain ⟨actualContent, contentEq, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  cases contentEq
  obtain ⟨⟨⟩, boundsOk, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨old, previous, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  simp only [bind, Option.bind, kindOk, freeOk, boundsOk, transfer old previous]
  exact accepted

theorem read?_gap_eq (left right : File.View) (base count content : Nat)
    (length : left.length = right.length)
    (countField : left.be? (base + 3) 2 = some count)
    (contentField : left.be? (base + 5) 2 = some content)
    (headerBytes : ∀ i, base ≤ i → i < base + 8 + 2 * count → left.get? i = right.get? i)
    (body : ∀ i, content ≤ i → i < left.length → left.get? i = right.get? i) :
    read? right base = read? left base := by
  cases original : read? left base with
  | some cells =>
    exact read?_gap_frame left right base count content cells original length
      countField contentField headerBytes body
  | none =>
    cases other : read? right base with
    | none => rfl
    | some cells =>
      have rightCount := (beTwo_eq left right (base + 3)
        (headerBytes _ (by omega) (by omega)) (headerBytes _ (by omega) (by omega))).symm.trans countField
      have rightContent := (beTwo_eq left right (base + 5)
        (headerBytes _ (by omega) (by omega)) (headerBytes _ (by omega) (by omega))).symm.trans contentField
      have backwards := read?_gap_frame right left base count content cells other length.symm
        rightCount rightContent (fun i lo hi => (headerBytes i lo hi).symm)
        (fun i lo hi => (body i lo (length.symm ▸ hi)).symm)
      simp [original] at backwards

end Silmaril.Proofs.Formats.Sqlite.TableLeaf.Frame
