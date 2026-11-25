module

public import Silmaril.SSA.RVSDG.Isomorphism.Defs

@[expose] public section

namespace Silmaril.SSA.RVSDG.Isomorphism.Proofs

universe u w

variable {Ty : Type u} {F : Ty → Type w}

-- Retain the type tag when comparing colours at corresponding numeric addresses.
def colours {ts : Ports Ty} : Tuple F ts → List (Sigma F)
  | .nil => []
  | @Tuple.cons _ _ t _ value rest => ⟨t, value⟩ :: colours rest

theorem colours_injective {ts : Ports Ty} (left right : Tuple F ts)
    (eq : colours left = colours right) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons val left ih =>
    cases right with
    | cons other right =>
      have head := (List.cons.inj eq).1
      have tail := (List.cons.inj eq).2
      have heads : val = other := by simpa only [Sigma.mk.injEq, true_and, heq_eq_eq] using head
      rw [heads, ih right tail]

theorem colours_get {ts : Ports Ty} {t : Ty} (tuple : Tuple F ts) (p : Port ts t) :
    (colours tuple)[p.index]? = some ⟨t, tuple.get p⟩ := by
  induction p with
  | head => cases tuple; rfl
  | tail p ih => cases tuple with | cons _ rest => exact ih rest

theorem prefix_get {α : Type w} {before all : List α} (h : before <+: all)
    {i : Nat} (bound : i < before.length) : all[i]? = before[i]? := by
  obtain ⟨rest, rfl⟩ := h
  exact List.getElem?_append_left bound

theorem source_before {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) {vertex port : Nat}
    (mem : Address.output vertex port ∈ wires.addresses) : vertex < past.length := by
  induction wires with
  | nil => cases mem
  | cons origin tail ih =>
    rcases List.mem_cons.mp mem with atHead | inTail
    · cases origin with
      | arg p => cases atHead
      | output i p =>
        have eq : vertex = i.val := (Address.output.inj atHead).1
        exact eq ▸ i.isLt
    · exact ih inTail

theorem site_length (past sigs : List (Ports Ty)) (i : Fin sigs.length) :
    (site past sigs i).1.length = past.length + i.val := by
  induction sigs generalizing past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (site (past ++ [head]) tail j).1.length = past.length + (j.val + 1)
      rw [ih, List.length_append, Nat.add_assoc, Nat.add_comm [_].length]
      rfl

theorem extend_length (past sigs : List (Ports Ty)) :
    (extend past sigs).length = past.length + sigs.length := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    change (extend (past ++ [head]) tail).length = past.length + (tail.length + 1)
    rw [ih, List.length_append, Nat.add_assoc, Nat.add_comm [_].length]
    rfl

end Silmaril.SSA.RVSDG.Isomorphism.Proofs
