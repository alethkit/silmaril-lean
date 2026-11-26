module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Defs

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs

open Local (Renaming)

private theorem position_assigned {rows : List RowPair} (distinct : rows.Pairwise RowPair.separate)
    {row : RowPair} (present : row ∈ rows) : completePositions rows row.left = row.right := by
  induction rows with
  | nil => cases present
  | cons head rest ih =>
    obtain ⟨different, distinctTail⟩ := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp present with rfl | inside
    · exact Equiv.swap_apply_left _ _
    · have assigned := ih distinctTail inside
      have separate := different row inside
      change Equiv.swap (completePositions rest head.left) head.right (completePositions rest row.left) = row.right
      rw [Equiv.swap_apply_of_ne_of_ne, assigned]
      · exact fun same => separate.1 ((completePositions rest).injective same).symm
      · rw [assigned]
        exact separate.2.symm

private theorem find_left {rows : List RowPair} (distinct : rows.Pairwise RowPair.separate)
    {row : RowPair} (present : row ∈ rows) : rows.find? (fun entry => entry.left == row.left) = some row := by
  induction rows with
  | nil => cases present
  | cons head rest ih =>
    obtain ⟨different, distinctTail⟩ := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp present with rfl | inside
    · simp
    · have separate := (different row inside).1
      simpa [List.find?_cons, separate] using ih distinctTail inside

theorem completeRows_assigned {rows : List RowPair} {map : Renaming}
    (completed : completeRows rows = some map) {row : RowPair} (present : row ∈ rows) :
    map.vertices row.left = row.right ∧ ∀ arm, map.child row.left arm = row.children[arm]?.getD .identity := by
  unfold completeRows at completed
  split at completed
  · rename_i distinct
    cases completed
    exact ⟨position_assigned distinct present, fun arm => by simp only [Renaming.child, find_left distinct present]⟩
  · cases completed

universe u v

open NestedTheta.Equality (OpcodeCode kindCode kind_injective)

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S} [DecidableEq (Ty V S)]
variable {args outs : Ports (Ty V S)} {pastL pastR sigsL sigsR : List (Ports (Ty V S))}
variable {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key]

theorem scan_assigned (budget : Nat) (map : Renaming)
    (left : Code Op args pastL sigsL outs) (right : Code Op args pastR sigsR outs)
    {rows : List RowPair} (aligned : alignRows budget left right = some rows)
    (accepted : (scan keys budget map left right).isSome = true) :
    ∀ row ∈ rows, map.vertices row.left = row.right := by
  induction budget generalizing args outs pastL pastR sigsL sigsR rows with
  | zero => cases aligned
  | succ budget ih =>
    cases hL : emptyHead left with
    | some head =>
      cases head with
      | intro wires tail =>
        simp (disch := assumption) only [alignRows.eq_2, scan.eq_2, Option.isSome_map] at aligned accepted
        exact ih tail right aligned accepted
    | none =>
      cases hR : emptyHead right with
      | some head =>
        cases head with
        | intro wires tail =>
          simp (disch := assumption) only [alignRows.eq_3, scan.eq_3, Option.isSome_map] at aligned accepted
          exact ih left tail aligned accepted
      | none =>
        cases left with
        | ret wiresL =>
          cases right with
          | ret wiresR =>
            rw [alignRows.eq_4] at aligned
            cases aligned
            intro _ member
            cases member
          | bind =>
            simp only [alignRows.eq_def, hL, hR] at aligned
            cases aligned
        | @bind _ headL _ _ _ nodeL childrenL restL =>
          cases right with
          | ret =>
            simp only [alignRows.eq_def, hL, hR] at aligned
            cases aligned
          | @bind _ headR _ _ _ nodeR childrenR restR =>
            obtain ⟨inputsL, kindL, wiresL, _⟩ := nodeL
            obtain ⟨inputsR, kindR, wiresR, _⟩ := nodeR
            simp (disch := assumption) only [alignRows.eq_5, scan.eq_5] at aligned accepted
            by_cases sameOut : headL = headR
            case neg => simp [sameOut] at accepted
            subst headR
            simp only at accepted
            by_cases sameIn : inputsL = inputsR
            case neg => simp [sameIn] at accepted
            subst inputsR
            simp only at accepted
            by_cases labels : kindCode keys kindL = kindCode keys kindR
            case neg => simp [labels] at accepted
            have kinds := kind_injective keys kindL kindR labels
            subst kindR
            simp only at aligned accepted
            by_cases position : map.vertices pastL.length = pastR.length
            case neg => simp [position] at accepted
            by_cases edges : wiresL.addresses.map (Address.rename map.vertices) = wiresR.addresses
            case neg => simp [position, edges] at accepted
            by_cases childrenPass : ∀ i : Fin kindL.arity,
                (scan keys budget (map.child pastL.length i.val) (childrenL i) (childrenR i)).isSome = true
            case neg => simp [position, edges, childrenPass] at accepted
            simp [position, edges, childrenPass, Option.isSome_map] at accepted
            obtain ⟨maps, _, pairedTail⟩ := Option.bind_eq_some_iff.mp aligned
            obtain ⟨tail, alignedTail, finished⟩ := Option.bind_eq_some_iff.mp pairedTail
            cases finished
            intro row member
            rcases List.mem_cons.mp member with rfl | present
            · exact position
            · exact ih restL restR alignedTail accepted row present

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Proofs
