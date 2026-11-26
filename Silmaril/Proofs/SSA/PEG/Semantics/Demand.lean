module

public import Silmaril.SSA.PEG.Semantics.Demand
public import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG.Semantics.Proofs

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}
variable {params results : List (Ty Data)} {n l : Nat}

private def RankVector : Nat → Type
  | 0 => Unit
  | k + 1 => Nat × RankVector k

private def RankLT : (k : Nat) → RankVector k → RankVector k → Prop
  | 0 => fun _ _ => False
  | k + 1 => Prod.Lex Nat.lt (RankLT k)

private theorem rankLT_wf (k : Nat) : WellFounded (RankLT k) := by
  induction k with
  | zero => exact ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  | succ k ih => exact ⟨fun q => Prod.lexAccessible (Nat.lt_wfRel.wf.apply q.1) ih.apply q.2⟩

private def rankValue : (rank : DemandRank n l) → Request n l → RankVector rank.length
  | [], _ => ()
  | c :: cs, q => (c.value q, rankValue cs q)

private theorem change_sound (c : RankComponent n l) (a b : Fin n) {kind : EdgeKind (Fin l)}
    {i j : Index l} (h : kind.Changes i j) :
    match c.change a b kind with
    | .lower => c.value (b, j) < c.value (a, i)
    | .equal => c.value (b, j) = c.value (a, i)
    | .unknown => True := by
  cases c with
  | phase rank =>
    by_cases lt : rank b < rank a
    · simp [RankComponent.change, RankComponent.value, lt]
    · by_cases eq : rank b = rank a <;> simp [RankComponent.change, RankComponent.value, lt, eq]
  | counter loop =>
    cases kind with
    | ordinary => obtain rfl := h; rfl
    | index _ => obtain rfl := h; rfl
    | initial _ => obtain ⟨_, rfl⟩ := h; rfl
    | feedback k =>
      obtain ⟨count, before, rfl⟩ := h
      by_cases eq : loop = k
      · subst loop
        simp [RankComponent.change, RankComponent.value, Index.set, before]
      · simp [RankComponent.change, RankComponent.value, Index.set, eq]
    | sample k =>
      obtain ⟨count, rfl⟩ := h
      by_cases eq : loop = k <;> simp [RankComponent.change, RankComponent.value, Index.set, eq]

private theorem checkEdge_decreases (rank : DemandRank n l) {a b : Fin n}
    {kind : EdgeKind (Fin l)} {i j : Index l} (change : kind.Changes i j)
    (check : rank.checkEdge a b kind = true) :
    RankLT rank.length (rankValue rank (b, j)) (rankValue rank (a, i)) := by
  induction rank with
  | nil => contradiction
  | cons c cs ih =>
    have sound := change_sound c a b change
    cases hc : c.change a b kind with
    | lower =>
      rw [hc] at sound
      exact Prod.Lex.left _ _ sound
    | equal =>
      rw [hc] at sound
      have rest := ih (by simpa [DemandRank.checkEdge, hc] using check)
      exact (Prod.lex_def).mpr (.inr ⟨sound, rest⟩)
    | unknown => simp [DemandRank.checkEdge, hc] at check

theorem demand_wf_of_check (g : Graph P params results n l) (rank : DemandRank n l)
    (check : rank.check g = true) : WellFounded g.Demand := by
  apply Subrelation.wf _ (InvImage.wf (rankValue rank) (rankLT_wf rank.length))
  rintro ⟨b, j⟩ ⟨a, i⟩ ⟨kind, ⟨slot, rfl, rfl⟩, change⟩
  obtain atNode := (List.all_eq_true.mp check) a (List.mem_finRange a)
  have atSlot := (List.all_eq_true.mp atNode) slot (List.mem_finRange slot)
  exact checkEdge_decreases rank change atSlot

private theorem mapKind_refl (k : EdgeKind (Fin l)) : k.map (Equiv.refl _) = k := by
  cases k <;> rfl

theorem demand_mapOps (g : Graph P params results n l) (f : InstructionMap P Q)
    (p q : Request n l) : (g.mapOps f).Demand p q ↔ g.Demand p q := by
  simp only [Graph.Demand, Graph.mapOps, g.edge_relabel, Equiv.refl_apply, mapKind_refl]

end Silmaril.SSA.PEG.Semantics.Proofs
