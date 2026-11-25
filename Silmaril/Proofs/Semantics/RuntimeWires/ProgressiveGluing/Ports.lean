module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Coordinates

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
section Ports

variable {U : ℕ} {P : Type*} {lower : Diagram S L W .point} {upper : Diagram S R U .point}

theorem generator_left (j : Fin L) : gluedGenerator lower upper (Fin.castAdd R j) = lower.generator j := by
  simp [gluedGenerator]

theorem generator_right (j : Fin R) : gluedGenerator lower upper (Fin.natAdd L j) = upper.generator j := by
  simp [gluedGenerator]

def ports (word : S.Edge → List O)
    (first : ∀ j, Fin (word (lower.generator j)).length → P)
    (last : ∀ j, Fin (word (upper.generator j)).length → P) :
    ∀ j, Fin (word (gluedGenerator lower upper j)).length → P :=
  Fin.addCases
    (fun j i => first j (i.cast (congrArg (fun e => (word e).length) (generator_left j))))
    (fun j i => last j (i.cast (congrArg (fun e => (word e).length) (generator_right j))))

theorem ports_left (word : S.Edge → List O) (j : Fin L)
    (first : ∀ j, Fin (word (lower.generator j)).length → P)
    (last : ∀ j, Fin (word (upper.generator j)).length → P)
    (i : Fin (word (gluedGenerator lower upper (Fin.castAdd R j))).length) :
    ports word first last (Fin.castAdd R j) i =
      first j (i.cast (congrArg (fun e => (word e).length) (generator_left j))) := by
  simp [ports]

theorem ports_right (word : S.Edge → List O) (j : Fin R)
    (first : ∀ j, Fin (word (lower.generator j)).length → P)
    (last : ∀ j, Fin (word (upper.generator j)).length → P)
    (i : Fin (word (gluedGenerator lower upper (Fin.natAdd L j))).length) :
    ports word first last (Fin.natAdd L j) i =
      last j (i.cast (congrArg (fun e => (word e).length) (generator_right j))) := by
  simp [ports]

theorem port_list_left (word : S.Edge → List O) (j : Fin L)
    (first : ∀ j, Fin (word (lower.generator j)).length → P)
    (last : ∀ j, Fin (word (upper.generator j)).length → P) :
    List.ofFn (ports word first last (Fin.castAdd R j)) = List.ofFn (first j) := by
  rw [List.ofFn_congr (congrArg (fun e => (word e).length) (generator_left j))]
  exact congrArg List.ofFn (funext fun i => by simp [ports_left])

theorem port_list_right (word : S.Edge → List O) (j : Fin R)
    (first : ∀ j, Fin (word (lower.generator j)).length → P)
    (last : ∀ j, Fin (word (upper.generator j)).length → P) :
    List.ofFn (ports word first last (Fin.natAdd L j)) = List.ofFn (last j) := by
  rw [List.ofFn_congr (congrArg (fun e => (word e).length) (generator_right j))]
  exact congrArg List.ofFn (funext fun i => by simp [ports_right])

end Ports

variable {lower : Diagram S L W .point} {upper : Diagram S R W .point}

theorem start_left (w : Fin W) (j : Fin L) :
    gluedStart (R := R) lower w = some (Fin.castAdd R j) ↔ lower.start w = some j := by
  cases h : lower.start w <;> simp [gluedStart, h, Fin.ext_iff]

theorem finish_right (w : Fin W) (j : Fin R) :
    gluedFinish (L := L) upper w = some (Fin.natAdd L j) ↔ upper.finish w = some j := by
  cases h : upper.finish w <;> simp [gluedFinish, h, Fin.ext_iff]

theorem left_ne_right (i : Fin L) (j : Fin R) : Fin.castAdd R i ≠ Fin.natAdd L j := by
  intro same
  have val := congrArg Fin.val same
  simp only [Fin.val_castAdd, Fin.val_natAdd] at val
  have bound := i.isLt
  omega

theorem start_not_right (w : Fin W) (j : Fin R) :
    gluedStart lower (R := R) w ≠ some (Fin.natAdd L j) := by
  cases h : lower.start w with
  | none => simp [gluedStart, h]
  | some i => simpa [gluedStart, h] using left_ne_right i j

theorem finish_not_left (w : Fin W) (j : Fin L) :
    gluedFinish (L := L) upper w ≠ some (Fin.castAdd R j) := by
  cases h : upper.finish w with
  | none => simp [gluedFinish, h]
  | some i => simpa [gluedFinish, h] using (left_ne_right j i).symm

variable (m : lower.VerticalMatch upper)
include m

theorem input_left_empty (j : Fin L) (i : Fin (S.source (lower.generator j)).length) : False := by
  have h := (lower.input_exact j (lower.input j i)).mpr ⟨i, rfl⟩
  rw [m.lower_cap] at h
  contradiction

theorem output_right_empty (j : Fin R) (i : Fin (S.target (upper.generator j)).length) : False := by
  have h := (upper.output_exact j (upper.output j i)).mpr ⟨i, rfl⟩
  rw [m.upper_cap] at h
  contradiction

theorem input_exact (j : Fin (L + R)) (w : Fin W) :
    gluedFinish upper (L := L) w = some j ↔ ∃ i, ports S.source lower.input upper.input j i = w := by
  rw [← List.mem_ofFn]
  induction j using Fin.addCases with
  | left v =>
    rw [port_list_left]
    exact (iff_of_false (finish_not_left w v) (fun h => by
      obtain ⟨i, _⟩ := List.mem_ofFn.mp h
      exact input_left_empty m v i))
  | right v =>
    rw [finish_right, port_list_right, List.mem_ofFn]
    exact upper.input_exact v w

theorem output_exact (j : Fin (L + R)) (w : Fin W) :
    gluedStart lower (R := R) w = some j ↔ ∃ i, ports S.target lower.output upper.output j i = w := by
  rw [← List.mem_ofFn]
  induction j using Fin.addCases with
  | left v =>
    rw [start_left, port_list_left, List.mem_ofFn]
    exact lower.output_exact v w
  | right v =>
    rw [port_list_right]
    exact (iff_of_false (start_not_right w v) (fun h => by
      obtain ⟨i, _⟩ := List.mem_ofFn.mp h
      exact output_right_empty m v i))

theorem input_types (j : Fin (L + R)) :
    (List.ofFn (ports S.source lower.input upper.input j)).map lower.label = S.source (gluedGenerator lower upper j) := by
  induction j using Fin.addCases with
  | left v =>
    rw [port_list_left, generator_left]
    exact lower.input_types v
  | right v =>
    rw [port_list_right, generator_right, funext m.label]
    exact upper.input_types v

theorem output_types (j : Fin (L + R)) :
    (List.ofFn (ports S.target lower.output upper.output j)).map lower.label = S.target (gluedGenerator lower upper j) := by
  induction j using Fin.addCases with
  | left v =>
    rw [port_list_left, generator_left]
    exact lower.output_types v
  | right v =>
    rw [port_list_right, generator_right, funext m.label]
    exact upper.output_types v

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
