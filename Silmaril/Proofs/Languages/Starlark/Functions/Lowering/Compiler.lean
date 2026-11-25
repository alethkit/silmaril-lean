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

private theorem advances_map {α β : Type} (f : α → β) {act : StateM Nat α} (h : Advances act) :
    Advances (f <$> act) := h

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
      have := List.sizeOf_lt_of_mem part.property
      exact advances_stage (advances_emit part.val)
    · intro _
      apply advances_bind
      · apply advances_many
        intro part _
        have := List.sizeOf_lt_of_mem part.property
        have := keywordSize part.val
        exact advances_bind (advances_stage (advances_emit part.val.2)) fun _ => advances_pure _
      · intro _
        cases star <;> cases starStar
        all_goals
          apply advances_bind
          · first | exact advances_pure _ | exact advances_map _ (advances_stage (advances_emit _))
          intro _
          apply advances_bind
          · first | exact advances_pure _ | exact advances_map _ (advances_stage (advances_emit _))
          intro _
          exact advances_pure _
termination_by sizeOf expr
decreasing_by all_goals (simp_wf; omega)

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

theorem emit_callPos (callee : Expr) (args : List Expr) (target : Binding) (start : Nat) :
    ((emit (.callPos callee args) target).run start).1 =
    let parts := ((stages (callee :: args)).run start).1
    (parts.map Prod.fst).foldr Body.seq
      (.call (some target) (scratchRead start) { positional := parts.tail.map Prod.snd }) := by
  rw [Expr.callPos, emit, stages_cons]
  have map : args.attach.mapM (fun part => stage (emit part.val)) =
      args.mapM (fun expr => stage (emit expr)) := by
    change args.attach.mapM ((fun expr => stage (emit expr)) ∘ Subtype.val) = _
    rw [← List.mapM_map]
    change args.attach.unattach.mapM _ = _
    rw [List.unattach_attach]
  simp only [map, stages, List.attach_nil, List.mapM_nil, StateT.run_bind, StateT.run_pure, stage_run]
  dsimp only [bind, pure]
  simp

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
