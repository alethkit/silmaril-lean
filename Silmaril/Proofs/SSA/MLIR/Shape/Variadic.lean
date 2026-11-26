module

public import Silmaril.SSA.MLIR.Shape.Variadic.Defs
import Silmaril.SSA.MLIR.Shape.Thms

public section

namespace Silmaril.Proofs.MLIR.Shape

open Silmaril.MLIR Shape

private theorem trailingExtent_of_ge (shape : Tensor.Shape) (axis : Nat)
    (outOfBounds : shape.length ≤ axis) : trailingExtent shape axis = 1 := by
  unfold trailingExtent
  rw [getElem?_neg shape.reverse axis (by simpa using Nat.not_lt.mpr outOfBounds)]
  rfl

private theorem trailingExtent_leftpad (shape : Tensor.Shape) (rank axis : Nat)
    (fits : shape.length ≤ rank) (inBounds : axis < rank) :
    trailingExtent shape axis = (shape.leftpad rank 1)[rank - 1 - axis]?.getD 1 := by
  unfold trailingExtent
  by_cases inShape : axis < shape.length
  · rw [List.getElem?_reverse inShape, List.leftpad,
      List.getElem?_append_right (by simp only [List.length_replicate]; omega),
      List.length_replicate]
    congr 2
    omega
  · rw [getElem?_neg shape.reverse axis (by simpa using inShape), List.leftpad,
      List.getElem?_append_left (by simp only [List.length_replicate]; omega),
      List.getElem?_replicate_of_lt (by omega)]
    rfl

private theorem trailingExtent_eq_of_leftpad (shape : Tensor.Shape) (rank axis extent : Nat)
    (rankEq : shape.length = rank) (inBounds : axis < rank)
    (atAxis : shape[rank - 1 - axis]? = some extent) : trailingExtent shape axis = extent := by
  rw [trailingExtent_leftpad shape rank axis (Nat.le_of_eq rankEq) inBounds,
    List.leftpad, rankEq, Nat.sub_self, List.replicate_zero, List.nil_append, atAxis]
  rfl

private theorem broadcastRank_cons (shape : Tensor.Shape) (shapes : List Tensor.Shape) :
    broadcastRank (shape :: shapes) = max shape.length (broadcastRank shapes) := rfl

private theorem length_le_broadcastRank {shape : Tensor.Shape} {shapes : List Tensor.Shape}
    (member : shape ∈ shapes) : shape.length ≤ broadcastRank shapes := by
  induction shapes with
  | nil => simp at member
  | cons first rest ih =>
    rw [broadcastRank_cons]
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

private theorem binary_axes {lhs rhs result : Tensor.Shape}
    (success : broadcastConcrete? lhs rhs = some result) :
    result.length = max lhs.length rhs.length ∧
      ∀ axis : Nat, BroadcastAxis [lhs, rhs] axis (trailingExtent result axis) := by
  obtain ⟨compatible, rankEq, atDim⟩ := Silmaril.MLIR.Shape.broadcastConcrete?_eq_some_iff _ _ _ |>.mp success
  refine ⟨rankEq, ?_⟩
  intro axis
  let rank := max lhs.length rhs.length
  by_cases inBounds : axis < rank
  · let dim : Fin rank := ⟨rank - 1 - axis, by omega⟩
    have left := trailingExtent_leftpad lhs rank axis (Nat.le_max_left _ _) inBounds
    have right := trailingExtent_leftpad rhs rank axis (Nat.le_max_right _ _) inBounds
    have atAxis := trailingExtent_eq_of_leftpad result rank axis _ rankEq inBounds (atDim dim)
    have compat := compatible dim
    rw [← left, ← right] at atAxis compat
    intro extent nonunit
    rw [atAxis]
    rcases compat with agrees | unitLeft | unitRight
    · simp [agrees]
    · simp [unitLeft, Ne.symm nonunit]
    · by_cases unitLeft : trailingExtent lhs axis = 1 <;> simp [unitLeft, unitRight, Ne.symm nonunit]
  · have lhsUnit := trailingExtent_of_ge lhs axis (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_not_gt inBounds))
    have rhsUnit := trailingExtent_of_ge rhs axis (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_not_gt inBounds))
    have resultUnit := trailingExtent_of_ge result axis (rankEq ▸ Nat.le_of_not_gt inBounds)
    intro extent nonunit
    simp [lhsUnit, rhsUnit, resultUnit, Ne.symm nonunit]

private theorem binary_conflict {lhs rhs : Tensor.Shape}
    (failure : broadcastConcrete? lhs rhs = none) :
    ∃ axis : Nat, trailingExtent lhs axis ≠ trailingExtent rhs axis ∧
      trailingExtent lhs axis ≠ 1 ∧ trailingExtent rhs axis ≠ 1 := by
  obtain ⟨dim, conflict⟩ := Silmaril.MLIR.Shape.broadcastConcrete?_eq_none_iff _ _ |>.mp failure
  let rank := max lhs.length rhs.length
  let axis := rank - 1 - dim.val
  have dimInBounds : dim.val < rank := dim.isLt
  have axisInBounds : axis < rank := by omega
  have index : rank - 1 - axis = dim.val := by omega
  refine ⟨axis, ?_⟩
  rw [trailingExtent_leftpad lhs rank axis (Nat.le_max_left _ _) axisInBounds,
    trailingExtent_leftpad rhs rank axis (Nat.le_max_right _ _) axisInBounds, index]
  exact conflict

private theorem axis_unique {shapes : List Tensor.Shape} {axis a b : Nat}
    (left : BroadcastAxis shapes axis a) (right : BroadcastAxis shapes axis b) : a = b := by
  by_cases leftUnit : a = 1
  · by_cases rightUnit : b = 1
    · exact leftUnit.trans rightUnit.symm
    · exact (left b rightUnit).mp ((right b rightUnit).mpr rfl)
  · exact ((right a leftUnit).mp ((left a leftUnit).mpr rfl)).symm

private theorem output_unique {shapes : List Tensor.Shape} {lhs rhs : Tensor.Shape}
    (left : BroadcastsManyTo shapes lhs) (right : BroadcastsManyTo shapes rhs) : lhs = rhs := by
  apply List.reverse_inj.mp
  apply List.ext_getElem (by simpa using left.1.trans right.1.symm)
  intro axis lhsInBounds rhsInBounds
  simpa only [trailingExtent, getElem?_pos lhs.reverse axis lhsInBounds,
    getElem?_pos rhs.reverse axis rhsInBounds, Option.getD_some] using
    axis_unique (left.2 axis) (right.2 axis)

private theorem compatible_of_axes {shapes : List Tensor.Shape}
    (axes : ∀ axis : Nat, ∃ extent, BroadcastAxis shapes axis extent) :
    BroadcastManyCompatible shapes := by
  intro axis lhs rhs lhsMem rhsMem lhsNonunit rhsNonunit
  obtain ⟨_, correct⟩ := axes axis
  exact ((correct _ lhsNonunit).mp ⟨lhs, lhsMem, rfl⟩).symm.trans
    ((correct _ rhsNonunit).mp ⟨rhs, rhsMem, rfl⟩)

private theorem collapse {lhs rhs merged : Tensor.Shape}
    (success : broadcastConcrete? lhs rhs = some merged) (rest : List Tensor.Shape)
    (result : Tensor.Shape) :
    BroadcastsManyTo (lhs :: rhs :: rest) result ↔ BroadcastsManyTo (merged :: rest) result := by
  obtain ⟨rankEq, axes⟩ := binary_axes success
  simp only [BroadcastsManyTo, broadcastRank_cons, rankEq, Nat.max_assoc]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro axis
  have occurs (value : Nat) (nonunit : value ≠ 1) :
      (∃ shape ∈ lhs :: rhs :: rest, trailingExtent shape axis = value) ↔
        (∃ shape ∈ merged :: rest, trailingExtent shape axis = value) := by
    have mergedExtent :
        trailingExtent lhs axis = value ∨ trailingExtent rhs axis = value ↔
          trailingExtent merged axis = value := by
      simpa using axes axis value nonunit
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left, ← mergedExtent, or_assoc]
  exact ⟨fun spec value nonunit => (occurs value nonunit).symm.trans (spec value nonunit),
    fun spec value nonunit => (occurs value nonunit).trans (spec value nonunit)⟩

private theorem foldl_eq_some_iff (first : Tensor.Shape) (rest : List Tensor.Shape)
    (result : Tensor.Shape) :
    rest.foldlM broadcastConcrete? first = some result ↔
      BroadcastsManyTo (first :: rest) result := by
  induction rest generalizing first with
  | nil =>
    have self : BroadcastsManyTo [first] first := by
      exact ⟨by simp [broadcastRank], fun axis value _ => by simp⟩
    change some first = some result ↔ _
    rw [Option.some.injEq]
    exact ⟨fun eq => eq ▸ self, output_unique self⟩
  | cons second tail ih =>
    simp only [List.foldlM_cons]
    change (broadcastConcrete? first second).bind (tail.foldlM broadcastConcrete?) = some result ↔ _
    cases binary : broadcastConcrete? first second with
    | none =>
      simp only [Option.bind_none, reduceCtorEq, false_iff]
      intro correct
      obtain ⟨axis, disagree, lhsNonunit, rhsNonunit⟩ := binary_conflict binary
      have compatible := compatible_of_axes fun dim => ⟨_, correct.2 dim⟩
      exact disagree (compatible axis first second (by simp) (by simp) lhsNonunit rhsNonunit)
    | some merged =>
      rw [Option.bind_some, ih]
      exact (collapse binary tail result).symm

theorem broadcastManyConcrete?_eq_some_iff (shapes : List Tensor.Shape) (result : Tensor.Shape) :
    broadcastManyConcrete? shapes = some result ↔ shapes ≠ [] ∧ BroadcastsManyTo shapes result := by
  cases shapes with
  | nil => simp [broadcastManyConcrete?]
  | cons first rest => simpa [broadcastManyConcrete?] using foldl_eq_some_iff first rest result

private theorem axis_exists {shapes : List Tensor.Shape} (compatible : BroadcastManyCompatible shapes)
    (axis : Nat) : ∃ extent, BroadcastAxis shapes axis extent := by
  classical
  by_cases hasNonunit : ∃ shape ∈ shapes, trailingExtent shape axis ≠ 1
  · obtain ⟨first, member, firstNonunit⟩ := hasNonunit
    refine ⟨trailingExtent first axis, fun value nonunit => ⟨?_, ?_⟩⟩
    · rintro ⟨shape, shapeMem, shapeExtent⟩
      exact (compatible axis first shape member shapeMem firstNonunit (shapeExtent.symm ▸ nonunit)).trans shapeExtent
    · exact fun same => ⟨first, member, same⟩
  · refine ⟨1, fun value nonunit => iff_of_false ?_ (Ne.symm nonunit)⟩
    rintro ⟨shape, member, atAxis⟩
    exact hasNonunit ⟨shape, member, atAxis.symm ▸ nonunit⟩

theorem compatible_iff_exists_broadcastsManyTo (shapes : List Tensor.Shape) :
    BroadcastManyCompatible shapes ↔ ∃ result : Tensor.Shape, BroadcastsManyTo shapes result := by
  constructor
  · intro compatible
    let extents := List.ofFn fun axis : Fin (broadcastRank shapes) => (axis_exists compatible axis).choose
    refine ⟨extents.reverse, by simp [extents], ?_⟩
    intro axis
    by_cases inBounds : axis < broadcastRank shapes
    · simpa [trailingExtent, extents, inBounds] using (axis_exists compatible axis).choose_spec
    · have resultUnit : trailingExtent extents.reverse axis = 1 :=
        trailingExtent_of_ge _ _ (by simpa [extents] using Nat.le_of_not_gt inBounds)
      intro value nonunit
      refine iff_of_false ?_ (resultUnit ▸ Ne.symm nonunit)
      rintro ⟨shape, member, atAxis⟩
      have unit := trailingExtent_of_ge shape axis
        (Nat.le_trans (length_le_broadcastRank member) (Nat.le_of_not_gt inBounds))
      exact nonunit (atAxis.symm.trans unit)
  · rintro ⟨result, correct⟩
    exact compatible_of_axes fun axis => ⟨trailingExtent result axis, correct.2 axis⟩

theorem broadcastManyConcrete?_isSome_iff (shapes : List Tensor.Shape) :
    (broadcastManyConcrete? shapes).isSome = true ↔ shapes ≠ [] ∧ BroadcastManyCompatible shapes := by
  rw [compatible_iff_exists_broadcastsManyTo]
  change (broadcastManyConcrete? shapes).isSome ↔ _
  simp [Option.isSome_iff_exists, broadcastManyConcrete?_eq_some_iff, exists_and_left]

theorem broadcastManyConcrete?_eq_none_iff (shapes : List Tensor.Shape) :
    broadcastManyConcrete? shapes = none ↔ shapes = [] ∨ ¬ BroadcastManyCompatible shapes := by
  classical
  rw [← Option.not_isSome_iff_eq_none, broadcastManyConcrete?_isSome_iff]
  by_cases empty : shapes = [] <;> simp [empty]

private theorem nil_iff_of_perm {α : Type} {lhs rhs : List α} (perm : lhs.Perm rhs) :
    lhs = [] ↔ rhs = [] :=
  ⟨fun eq => (eq ▸ perm.symm).eq_nil, fun eq => (eq ▸ perm).eq_nil⟩

theorem broadcastManyConcrete?_perm {lhs rhs : List Tensor.Shape} (perm : lhs.Perm rhs) :
    broadcastManyConcrete? lhs = broadcastManyConcrete? rhs := by
  have sameRank : broadcastRank lhs = broadcastRank rhs :=
    perm.foldr_eq' (fun a _ b _ rank => Nat.max_left_comm b.length a.length rank) 0
  have sameSuccess (result : Tensor.Shape) :
      broadcastManyConcrete? lhs = some result ↔ broadcastManyConcrete? rhs = some result := by
    simp only [broadcastManyConcrete?_eq_some_iff, not_congr (nil_iff_of_perm perm), BroadcastsManyTo,
      BroadcastAxis, sameRank, perm.mem_iff]
  cases left : broadcastManyConcrete? lhs with
  | some value => exact ((sameSuccess value).mp left).symm
  | none =>
    cases right : broadcastManyConcrete? rhs with
    | none => rfl
    | some value =>
      have impossible := (sameSuccess value).mpr right
      simp [left] at impossible

private theorem mapM_toStatic_ofStatic (shapes : List Tensor.Shape) :
    (shapes.map ShapeValue.ofStatic).mapM ShapeValue.toStatic? = some shapes := by
  induction shapes <;> simp [ShapeValue.toStatic?_ofStatic, *]

private theorem invalid_not_mem_ofStatic (shapes : List Tensor.Shape) :
    ShapeValue.invalid ∉ shapes.map ShapeValue.ofStatic := by
  simp [List.mem_map, ShapeValue.ofStatic]

private theorem broadcastMany_ofStatic (shapes : List Tensor.Shape) :
    broadcastMany? (shapes.map ShapeValue.ofStatic) =
      if shapes = [] then none else
        some (((broadcastManyConcrete? shapes).map ShapeValue.ofStatic).getD .invalid) := by
  cases shapes with
  | nil => rfl
  | cons first rest =>
    rw [ite_eq_right (List.cons_ne_nil first rest)]
    change (if ShapeValue.invalid ∈ (first :: rest).map ShapeValue.ofStatic then
      some ShapeValue.invalid else ((first :: rest).map ShapeValue.ofStatic |>.mapM ShapeValue.toStatic?).map _) = _
    rw [ite_eq_right (invalid_not_mem_ofStatic (first :: rest)), mapM_toStatic_ofStatic]
    rfl

theorem broadcastMany?_ofStatic_eq_some_iff (shapes : List Tensor.Shape) (result : Tensor.Shape) :
    broadcastMany? (shapes.map ShapeValue.ofStatic) = some (.ofStatic result) ↔
      shapes ≠ [] ∧ BroadcastsManyTo shapes result := by
  rw [← broadcastManyConcrete?_eq_some_iff, broadcastMany_ofStatic]
  by_cases empty : shapes = []
  · simp [empty, broadcastManyConcrete?]
  · rw [ite_eq_right empty]
    cases broadcastManyConcrete? shapes <;> simp [ShapeValue.ofStatic, List.map_inj_right (fun _ _ => Option.some.inj)]

theorem broadcastMany?_ofStatic_eq_invalid_iff (shapes : List Tensor.Shape) :
    broadcastMany? (shapes.map ShapeValue.ofStatic) = some .invalid ↔
      shapes ≠ [] ∧ ¬ BroadcastManyCompatible shapes := by
  rw [broadcastMany_ofStatic]
  by_cases empty : shapes = []
  · simp [empty]
  · have failed : broadcastManyConcrete? shapes = none ↔ ¬ BroadcastManyCompatible shapes :=
      (broadcastManyConcrete?_eq_none_iff shapes).trans (by simp [empty])
    rw [ite_eq_right empty, and_iff_right empty, ← failed]
    cases broadcastManyConcrete? shapes <;> simp [ShapeValue.ofStatic]

theorem broadcastMany?_invalid {inputs : List ShapeValue} (invalid : ShapeValue.invalid ∈ inputs) :
    broadcastMany? inputs = some .invalid := by
  cases inputs with
  | nil => simp at invalid
  | cons first rest => simp [broadcastMany?, invalid]

theorem broadcastMany?_ofStatic_perm {lhs rhs : List Tensor.Shape} (perm : lhs.Perm rhs) :
    broadcastMany? (lhs.map ShapeValue.ofStatic) = broadcastMany? (rhs.map ShapeValue.ofStatic) := by
  simp only [broadcastMany_ofStatic, broadcastManyConcrete?_perm perm, nil_iff_of_perm perm]

private theorem broadcastManyExtentTensor_eval (inputs : List ExtentTensor) :
    broadcastManyExtentTensor? inputs = if inputs = [] then none else some (
      match broadcastManyConcrete? (inputs.map ExtentTensor.toShape) with
      | some shape => .defined (extentTensor shape)
      | none => .undefined) := by
  cases inputs <;> rfl

theorem broadcastManyExtentTensor?_eq_defined_iff (inputs : List ExtentTensor) (result : ExtentTensor) :
    broadcastManyExtentTensor? inputs = some (.defined result) ↔
      inputs ≠ [] ∧ BroadcastsManyTo (inputs.map ExtentTensor.toShape) result.toShape := by
  have encode {shape : Tensor.Shape} : extentTensor shape = result ↔ shape = result.toShape :=
    ⟨fun h => by rw [← h, ExtentTensor.toShape_extentTensor],
      fun h => h ▸ ExtentTensor.extentTensor_toShape result⟩
  have nonempty : (inputs.map ExtentTensor.toShape) ≠ [] ↔ inputs ≠ [] :=
    not_congr List.map_eq_nil_iff
  rw [broadcastManyExtentTensor_eval, ← nonempty, ← broadcastManyConcrete?_eq_some_iff]
  by_cases empty : inputs = []
  · simp [empty, broadcastManyConcrete?]
  · rw [ite_eq_right empty]
    cases broadcastManyConcrete? (inputs.map ExtentTensor.toShape) <;> simp [encode]

theorem broadcastManyExtentTensor?_eq_undefined_iff (inputs : List ExtentTensor) :
    broadcastManyExtentTensor? inputs = some .undefined ↔
      inputs ≠ [] ∧ ¬ BroadcastManyCompatible (inputs.map ExtentTensor.toShape) := by
  rw [broadcastManyExtentTensor_eval]
  by_cases empty : inputs = []
  · simp [empty]
  · have failed : broadcastManyConcrete? (inputs.map ExtentTensor.toShape) = none ↔
        ¬ BroadcastManyCompatible (inputs.map ExtentTensor.toShape) :=
      (broadcastManyConcrete?_eq_none_iff (inputs.map ExtentTensor.toShape)).trans (by simp [empty])
    rw [ite_eq_right empty, and_iff_right empty, ← failed]
    cases broadcastManyConcrete? (inputs.map ExtentTensor.toShape) <;> simp

theorem broadcastManyExtentTensor?_perm {lhs rhs : List ExtentTensor} (perm : lhs.Perm rhs) :
    broadcastManyExtentTensor? lhs = broadcastManyExtentTensor? rhs := by
  simp only [broadcastManyExtentTensor_eval, broadcastManyConcrete?_perm (perm.map ExtentTensor.toShape),
    nil_iff_of_perm perm]

private theorem isBroadcastableMany_ofStatic (shapes : List Tensor.Shape) :
    isBroadcastableMany? (shapes.map ShapeValue.ofStatic) =
      some (shapes.isEmpty || (broadcastManyConcrete? shapes).isSome) := by
  rw [isBroadcastableMany?, mapM_toStatic_ofStatic]
  rfl

theorem isBroadcastableMany?_ofStatic_eq_true_iff (shapes : List Tensor.Shape) :
    isBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some true ↔
      BroadcastManyCompatible shapes := by
  rw [isBroadcastableMany_ofStatic]
  cases shapes with
  | nil => simp [BroadcastManyCompatible]
  | cons first rest => simp [broadcastManyConcrete?_isSome_iff]

theorem isBroadcastableMany?_ofStatic_eq_false_iff (shapes : List Tensor.Shape) :
    isBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some false ↔
      ¬ BroadcastManyCompatible shapes := by
  rw [← isBroadcastableMany?_ofStatic_eq_true_iff, isBroadcastableMany_ofStatic]
  simp [Bool.not_eq_true]

theorem isBroadcastableMany?_ofStatic_perm {lhs rhs : List Tensor.Shape} (perm : lhs.Perm rhs) :
    isBroadcastableMany? (lhs.map ShapeValue.ofStatic) = isBroadcastableMany? (rhs.map ShapeValue.ofStatic) := by
  have sameEmpty : lhs.isEmpty = rhs.isEmpty := by
    cases lhs <;> cases rhs <;> simp_all
  simp only [isBroadcastableMany_ofStatic, sameEmpty, broadcastManyConcrete?_perm perm]

theorem cstrBroadcastableMany?_passing_iff (shapes : List Tensor.Shape) :
    cstrBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some .passing ↔
      2 ≤ shapes.length ∧ BroadcastManyCompatible shapes := by
  rw [cstrBroadcastableMany?, List.length_map, ← isBroadcastableMany?_ofStatic_eq_true_iff,
    isBroadcastableMany_ofStatic]
  by_cases arity : 2 ≤ shapes.length
  · rw [ite_eq_left arity, and_iff_right arity]
    cases (shapes.isEmpty || (broadcastManyConcrete? shapes).isSome) <;> simp
  · simp [arity]

theorem cstrBroadcastableMany?_unsatisfied_iff (shapes : List Tensor.Shape) :
    cstrBroadcastableMany? (shapes.map ShapeValue.ofStatic) = some .unsatisfied ↔
      2 ≤ shapes.length ∧ ¬ BroadcastManyCompatible shapes := by
  rw [cstrBroadcastableMany?, List.length_map, ← isBroadcastableMany?_ofStatic_eq_false_iff,
    isBroadcastableMany_ofStatic]
  by_cases arity : 2 ≤ shapes.length
  · rw [ite_eq_left arity, and_iff_right arity]
    cases (shapes.isEmpty || (broadcastManyConcrete? shapes).isSome) <;> simp
  · simp [arity]

theorem broadcastManyConcrete?_pair (lhs rhs : Tensor.Shape) :
    broadcastManyConcrete? [lhs, rhs] = broadcastConcrete? lhs rhs := by
  simp only [broadcastManyConcrete?, List.foldlM_cons, List.foldlM_nil]
  cases broadcastConcrete? lhs rhs <;> rfl

theorem broadcastMany?_pair (lhs rhs : ShapeValue) :
    broadcastMany? [lhs, rhs] = broadcast? lhs rhs := by
  cases lhs <;> cases rhs <;> simp [broadcastMany?, broadcast?, ShapeValue.toStatic?]
  rename_i lhs rhs
  cases List.mapM id lhs <;> cases List.mapM id rhs <;> simp [broadcastManyConcrete?_pair]

theorem broadcastManyExtentTensor?_pair (lhs rhs : ExtentTensor) :
    broadcastManyExtentTensor? [lhs, rhs] = some (broadcastExtentTensor lhs rhs) := by
  simp [broadcastManyExtentTensor?, broadcastExtentTensor, broadcastManyConcrete?_pair] <;> rfl

theorem isBroadcastableMany?_pair (lhs rhs : ShapeValue) :
    isBroadcastableMany? [lhs, rhs] = isBroadcastable? lhs rhs := by
  cases left : lhs.toStatic? <;> cases right : rhs.toStatic? <;>
    simp [isBroadcastableMany?, isBroadcastable?, left, right, broadcastManyConcrete?_pair]

end Silmaril.Proofs.MLIR.Shape
