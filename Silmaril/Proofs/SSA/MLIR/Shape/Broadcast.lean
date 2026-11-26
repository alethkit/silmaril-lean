module

public import Silmaril.SSA.MLIR.Shape.Defs

public section

namespace Silmaril.Proofs.MLIR.Shape

open Silmaril.MLIR Shape

private theorem alignedExtents_length (lhs rhs : Tensor.Shape) :
    (alignedExtents lhs rhs).length = max lhs.length rhs.length := by
  simp only [alignedExtents, List.length_zip, List.length_leftpad,
    Nat.max_eq_left (Nat.le_max_left lhs.length rhs.length),
    Nat.max_eq_left (Nat.le_max_right lhs.length rhs.length), Nat.min_self]

private theorem alignedExtents_at (lhs rhs : Tensor.Shape)
    (dim : Fin (max lhs.length rhs.length)) :
    let rank := max lhs.length rhs.length
    (alignedExtents lhs rhs)[dim.val]? =
      some ((lhs.leftpad rank 1)[dim.val]?.getD 1, (rhs.leftpad rank 1)[dim.val]?.getD 1) := by
  let rank := max lhs.length rhs.length
  have leftInBounds : dim.val < (lhs.leftpad rank 1).length := by
    rw [List.length_leftpad, Nat.max_eq_left (Nat.le_max_left lhs.length rhs.length)]
    exact dim.isLt
  have rightInBounds : dim.val < (rhs.leftpad rank 1).length := by
    rw [List.length_leftpad, Nat.max_eq_left (Nat.le_max_right lhs.length rhs.length)]
    exact dim.isLt
  change (alignedExtents lhs rhs)[dim.val]? =
    some ((lhs.leftpad rank 1)[dim.val]?.getD 1, (rhs.leftpad rank 1)[dim.val]?.getD 1)
  change ((lhs.leftpad rank 1).zip (rhs.leftpad rank 1))[dim.val]? = _
  rw [List.getElem?_zip_eq_some, getElem?_pos (lhs.leftpad rank 1) dim.val leftInBounds,
    getElem?_pos (rhs.leftpad rank 1) dim.val rightInBounds]
  simp

private theorem alignedExtents_all_iff (lhs rhs : Tensor.Shape) :
    (alignedExtents lhs rhs).all (fun (a, b) => a == b || a == 1 || b == 1) = true ↔
      BroadcastCompatible lhs rhs := by
  simp only [List.all_eq_true, List.mem_iff_getElem?, BroadcastCompatible]
  constructor
  · intro compatible dim
    simpa [or_assoc] using compatible _ ⟨dim.val, alignedExtents_at lhs rhs dim⟩
  · rintro compatible pair ⟨dim, atDim⟩
    have inBounds := (List.getElem?_eq_some_iff.mp atDim).choose
    rw [alignedExtents_length] at inBounds
    rw [alignedExtents_at lhs rhs ⟨dim, inBounds⟩] at atDim
    cases Option.some.inj atDim
    simpa [or_assoc] using compatible ⟨dim, inBounds⟩

theorem broadcastConcrete?_eq_some_iff (lhs rhs result : Tensor.Shape) :
    broadcastConcrete? lhs rhs = some result ↔ BroadcastsTo lhs rhs result := by
  simp only [broadcastConcrete?]
  split
  next allCompatible =>
    have compatible := (alignedExtents_all_iff lhs rhs).mp allCompatible
    simp only [Option.some.injEq, BroadcastsTo, compatible, true_and]
    constructor
    · rintro rfl
      exact ⟨by simp [alignedExtents_length], fun dim => by
        rw [List.getElem?_map, alignedExtents_at lhs rhs dim]; rfl⟩
    · rintro ⟨resultRank, atDim⟩
      apply List.ext_getElem?
      intro dim
      by_cases inBounds : dim < max lhs.length rhs.length
      · rw [atDim ⟨dim, inBounds⟩, List.getElem?_map, alignedExtents_at lhs rhs ⟨dim, inBounds⟩]
        rfl
      · simp [getElem?_neg, alignedExtents_length, resultRank, inBounds]
  next notAllCompatible =>
    simp [BroadcastsTo, ← alignedExtents_all_iff, notAllCompatible]

theorem broadcastConcrete?_eq_none_iff (lhs rhs : Tensor.Shape) :
    broadcastConcrete? lhs rhs = none ↔
      ∃ dim : Fin (max lhs.length rhs.length),
        let rank := max lhs.length rhs.length
        let a := (lhs.leftpad rank 1)[dim.val]?.getD 1
        let b := (rhs.leftpad rank 1)[dim.val]?.getD 1
        a ≠ b ∧ a ≠ 1 ∧ b ≠ 1 := by
  simp only [broadcastConcrete?, ite_eq_right_iff, reduceCtorEq, imp_false,
    Bool.not_eq_true, List.all_eq_false, List.mem_iff_getElem?]
  constructor
  · rintro ⟨pair, ⟨dim, atDim⟩, incompatible⟩
    have inBounds := (List.getElem?_eq_some_iff.mp atDim).choose
    rw [alignedExtents_length] at inBounds
    rw [alignedExtents_at lhs rhs ⟨dim, inBounds⟩] at atDim
    cases Option.some.inj atDim
    exact ⟨⟨dim, inBounds⟩, by simpa [and_assoc] using incompatible⟩
  · rintro ⟨dim, incompatible⟩
    exact ⟨_, ⟨dim.val, alignedExtents_at lhs rhs dim⟩, by simpa [and_assoc] using incompatible⟩

end Silmaril.Proofs.MLIR.Shape
