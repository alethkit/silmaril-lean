module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Frame

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding LogicalOp)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering

private def Advances {α : Type} (act : StateM Nat α) : Prop :=
  ∀ start, start ≤ (act.run start).2

private theorem advances_pure {α : Type} (value : α) : Advances (pure value) :=
  fun _ => Nat.le_refl _

private theorem advances_bind {α β : Type} {act : StateM Nat α} {next : α → StateM Nat β}
    (h : Advances act) (k : ∀ value, Advances (next value)) : Advances (act >>= next) :=
  fun start => Nat.le_trans (h start) (k (act.run start).1 (act.run start).2)

private theorem advances_many {α β : Type} (items : List α) (act : α → StateM Nat β)
    (h : ∀ item, item ∈ items → Advances (act item)) : Advances (items.mapM act) := by
  induction items with
  | nil => exact advances_pure []
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact advances_bind (h item (by simp)) fun value =>
      advances_bind (ih fun a ha => h a (by simp [ha])) fun values => advances_pure (value :: values)

@[expose] def scratchRead (index : Nat) : Languages.Starlark.Lists.Expr :=
  .read (.bound (temporary index))

theorem stage_run (code : Binding → StateM Nat Body) (start : Nat) :
    (stage code).run start =
      ((((code (temporary start)).run (start + 1)).1, scratchRead start),
        ((code (temporary start)).run (start + 1)).2) := rfl

private theorem advances_stage {code : Binding → StateM Nat Body}
    (h : ∀ b, Advances (code b)) : Advances (stage code) := by
  intro start
  rw [stage_run]
  exact Nat.le_trans (Nat.le_succ _) (h (temporary start) (start + 1))

private theorem advances_emit (expr : Expr) (target : Binding) :
    Advances (emit expr target) := by
  cases expr with
  | atom atom =>
    rw [emit]
    exact advances_pure _
  | list elements =>
    rw [emit]
    apply advances_bind
    · apply advances_many
      intro element _
      have := List.sizeOf_lt_of_mem element.property
      exact advances_stage (advances_emit element.val)
    · intro _
      exact advances_pure _
  | tuple elements =>
    rw [emit]
    apply advances_bind
    · apply advances_many
      intro element _
      have := List.sizeOf_lt_of_mem element.property
      exact advances_stage (advances_emit element.val)
    · intro _
      exact advances_pure _
  | index receiver subscript =>
    rw [emit]
    refine advances_bind (advances_stage (advances_emit receiver)) ?_
    rintro ⟨_, _⟩
    refine advances_bind (advances_stage (advances_emit subscript)) ?_
    rintro ⟨_, _⟩
    exact advances_pure _
  | branch test yes no =>
    rw [emit]
    refine advances_bind (advances_stage (advances_emit test)) fun saved => ?_
    rcases saved with ⟨_, _⟩
    exact advances_bind (advances_emit yes target) fun _ =>
      advances_bind (advances_emit no target) fun _ => advances_pure _
  | logical op left right =>
    rw [emit]
    refine advances_bind (advances_stage (advances_emit left)) fun saved => ?_
    rcases saved with ⟨_, _⟩
    exact advances_bind (advances_emit right target) fun _ => advances_pure _
  | call callee positional keywords star starStar =>
    rw [emit]
    refine advances_bind (advances_stage (advances_emit callee)) fun saved => ?_
    rcases saved with ⟨_, _⟩
    apply advances_bind
    · apply advances_many
      intro part _
      have := argumentSize callee positional keywords star starStar part.property
      exact advances_stage (advances_emit part.val)
    · intro _
      exact advances_pure _
termination_by sizeOf expr
decreasing_by all_goals first | assumption | (simp_wf; omega)

theorem emit_ge (expr : Expr) (target : Binding) (start : Nat) :
    start ≤ ((emit expr target).run start).2 :=
  advances_emit expr target start

@[expose] def stages (expressions : List Expr) : StateM Nat (List (Body × Languages.Starlark.Lists.Expr)) :=
  expressions.mapM fun expr => stage (emit expr)

theorem stages_cons (head : Expr) (tail : List Expr) (start : Nat) :
    (stages (head :: tail)).run start =
      let first := (emit head (temporary start)).run (start + 1)
      let rest := (stages tail).run first.2
      ((first.1, scratchRead start) :: rest.1, rest.2) := by
  unfold stages
  rw [List.mapM_cons]
  rfl

theorem stages_ge (expressions : List Expr) (start : Nat) :
    start ≤ ((stages expressions).run start).2 :=
  advances_many expressions _ (fun e _ => advances_stage (advances_emit e)) start

theorem stages_length (expressions : List Expr) (start : Nat) :
    ((stages expressions).run start).1.length = expressions.length := by
  induction expressions generalizing start with
  | nil => rfl
  | cons head tail ih =>
    simp only [stages_cons, List.length_cons, ih]

theorem emit_list (elements : List Expr) (target : Binding) (start : Nat) :
    ((emit (.list elements) target).run start).1 =
    let parts := ((stages elements).run start).1
    (parts.map Prod.fst).foldr Body.seq (assign target (.list (operandList (parts.map Prod.snd)))) := by
  let stageOne := fun expr : Expr => stage (emit expr)
  have traverse : elements.attach.mapM (stageOne ∘ Subtype.val) = elements.mapM stageOne := by
    rw [← List.mapM_map]
    change elements.attach.unattach.mapM stageOne = _
    rw [List.unattach_attach]
  rw [emit]
  change ((elements.attach.mapM (stageOne ∘ Subtype.val) >>= _) start).1 = _
  rw [traverse]
  rfl

theorem emit_tuple (elements : List Expr) (target : Binding) (start : Nat) :
    ((emit (.tuple elements) target).run start).1 =
    let parts := ((stages elements).run start).1
    (parts.map Prod.fst).foldr Body.seq (assign target (.tuple (operandList (parts.map Prod.snd)))) := by
  let stageOne := fun expr : Expr => stage (emit expr)
  have traverse : elements.attach.mapM (stageOne ∘ Subtype.val) = elements.mapM stageOne := by
    rw [← List.mapM_map]
    change elements.attach.unattach.mapM stageOne = _
    rw [List.unattach_attach]
  rw [emit]
  change ((elements.attach.mapM (stageOne ∘ Subtype.val) >>= _) start).1 = _
  rw [traverse]
  rfl

theorem emit_index (receiver subscript : Expr) (target : Binding) (start : Nat) :
    ((emit (.index receiver subscript) target).run start).1 =
    let parts := ((stages [receiver, subscript]).run start).1
    let next := ((emit receiver (temporary start)).run (start + 1)).2
    (parts.map Prod.fst).foldr Body.seq (assign target (.index (scratchRead start) (scratchRead next))) := by
  rw [emit]
  simp only [stages_cons]
  rfl

theorem emit_call (callee : Expr) (positional : List Expr) (keywords : List (String × Expr))
    (star starStar : Option Expr) (target : Binding) (start : Nat) :
    ((emit (.call callee positional keywords star starStar) target).run start).1 =
    let parts := ((stages (callee :: argumentExprs positional keywords star starStar)).run start).1
    let args := fillArguments (argumentShape positional keywords star starStar) (parts.tail.map Prod.snd)
    (parts.map Prod.fst).foldr Body.seq (.call (some target) (scratchRead start) args) := by
  rw [emit, stages_cons]
  let args := argumentExprs positional keywords star starStar
  have map : args.attach.mapM (fun part => stage (emit part.val)) =
      args.mapM (fun expr => stage (emit expr)) := by
    change args.attach.mapM ((fun expr => stage (emit expr)) ∘ Subtype.val) = _
    rw [← List.mapM_map]
    change args.attach.unattach.mapM _ = _
    rw [List.unattach_attach]
  dsimp only [args] at map
  simp only [map, stages, StateT.run_bind, StateT.run_pure, stage_run]
  rfl

theorem argument_count (positional : List Expr) (keywords : List (String × Expr))
    (star starStar : Option Expr) :
    (argumentExprs positional keywords star starStar).length =
      (argumentShape positional keywords star starStar).count := by
  cases star <;> cases starStar <;> simp [argumentExprs, argumentShape, ArgumentShape.count, Bool.toNat, Nat.add_assoc]

private theorem fill_spreads {α : Type} (star starStar : Bool) (values : List α)
    (length : values.length = star.toNat + starStar.toNat) :
    let spread := if star then values[0]? else none
    let mapping := if starStar then values[star.toNat]? else none
    spread.isSome = star ∧ mapping.isSome = starStar ∧ spread.toList ++ mapping.toList = values := by
  cases star <;> cases starStar <;>
    cases values with
    | nil => simp_all [Bool.toNat]
    | cons first rest =>
      cases rest with
      | nil => simp_all [Bool.toNat]
      | cons second rest =>
        cases rest <;> simp_all [Bool.toNat]

theorem fill_arguments (shape : ArgumentShape) (reads : List Languages.Starlark.Lists.Expr)
    (length : reads.length = shape.count) :
    (fillArguments shape reads).shape = shape ∧ (fillArguments shape reads).ordered = reads := by
  let afterPos := reads.drop shape.positional
  let trailing := afterPos.drop shape.keywords.length
  have enoughPos : shape.positional ≤ reads.length := by
    simp only [ArgumentShape.count] at length
    omega
  have enoughNames : shape.keywords.length ≤ afterPos.length := by
    simp only [afterPos, List.length_drop, ArgumentShape.count] at length ⊢
    omega
  have trailingLen : trailing.length = shape.star.toNat + shape.starStar.toNat := by
    simp only [trailing, afterPos, List.length_drop, ArgumentShape.count] at length ⊢
    omega
  let spread := if shape.star then trailing[0]? else none
  let mapping := if shape.starStar then trailing[shape.star.toNat]? else none
  obtain ⟨hs, hm, ordered⟩ := fill_spreads shape.star shape.starStar trailing trailingLen
  have nameLen : (afterPos.take shape.keywords.length).length = shape.keywords.length := by
    rw [List.length_take, Nat.min_eq_left enoughNames]
  let named := shape.keywords.zip (afterPos.take shape.keywords.length)
  have names : named.map Prod.fst = shape.keywords :=
    List.map_fst_zip (Nat.le_of_eq nameLen.symm)
  have nameReads : named.map Prod.snd = afterPos.take shape.keywords.length :=
    List.map_snd_zip (Nat.le_of_eq nameLen)
  constructor
  · change ArgumentShape.mk (reads.take shape.positional).length (named.map Prod.fst)
      spread.isSome mapping.isSome = shape
    rw [List.length_take, Nat.min_eq_left enoughPos, names]
    have hs' : spread.isSome = shape.star := hs
    have hm' : mapping.isSome = shape.starStar := hm
    rw [hs', hm']
  · change reads.take shape.positional ++ named.map Prod.snd ++ spread.toList ++ mapping.toList = reads
    have tailReads : spread.toList ++ mapping.toList = trailing := ordered
    simp only [nameReads, List.append_assoc, tailReads]
    change reads.take shape.positional ++
      (afterPos.take shape.keywords.length ++ afterPos.drop shape.keywords.length) = reads
    rw [List.take_append_drop, List.take_append_drop]

theorem emit_atom (expr : Languages.Starlark.Lists.Expr) (target : Binding) (start : Nat) :
    ((emit (.atom expr) target).run start).1 = assign target expr := by
  rw [emit]
  rfl

theorem emit_branch (test yes no : Expr) (target : Binding) (start : Nat) :
    ((emit (.branch test yes no) target).run start).1 =
    let first := (emit test (temporary start)).run (start + 1)
    let left := (emit yes target).run first.2
    let right := (emit no target).run left.2
    .seq first.1 (.branch (scratchRead start) left.1 right.1) := by
  rw [emit]
  rfl

theorem emit_logical (op : LogicalOp) (left right : Expr) (target : Binding) (start : Nat) :
    ((emit (.logical op left right) target).run start).1 =
    let first := (emit left (temporary start)).run (start + 1)
    let second := (emit right target).run first.2
    let keep := assign target (scratchRead start)
    .seq first.1 (match op with
      | .and => .branch (scratchRead start) second.1 keep
      | .or => .branch (scratchRead start) keep second.1) := by
  rw [emit]
  rfl

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
