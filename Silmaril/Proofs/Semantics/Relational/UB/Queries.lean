module

public import Silmaril.Semantics.Relational.UB.QueryDefs
public import Silmaril.Semantics.Relational.UB.Thms
public import Silmaril.Semantics.Relational.Query.Thms

public section

namespace Silmaril.Proofs.Relational.UB

open Silmaril.Relational Silmaril.Relational.UB

variable {DB Small Large Result Reason : Type*}

theorem le_extendQueries_iff {Value : Type*} [LE Value] (embedding : Small ↪ Large)
    (fallback : DB → Large → Value) (small : DB → Small → Value) (large : DB → Large → Value) :
    large ≤ extendQueries embedding fallback small ↔
      (∀ db query, large db (embedding query) ≤ small db query) ∧
      (∀ db query, (¬ ∃ q, embedding q = query) → large db query ≤ fallback db query) := by
  constructor
  · intro refine
    exact ⟨fun db q => (extendQueries_apply_image embedding fallback small db q) ▸ refine db (embedding q),
      fun db q outside => (extendQueries_apply_outside embedding fallback small db q outside) ▸ refine db q⟩
  · intro ⟨inside_le, outside_le⟩ db query
    by_cases h : ∃ q, embedding q = query
    · obtain ⟨q, rfl⟩ := h
      rw [extendQueries_apply_image]
      exact inside_le db q
    · rw [extendQueries_apply_outside _ _ _ _ _ h]
      exact outside_le db query h

theorem restrict_eq_iff {Value : Type*} (translate : Small → Large)
    (left right : DB → Large → Value) :
    (fun db query => left db (translate query)) = (fun db query => right db (translate query)) ↔
    ∀ db query, (∃ q, translate q = query) → left db query = right db query := by
  constructor
  · intro eq db query ⟨q, imageEq⟩
    subst query
    exact congrFun (congrFun eq db) q
  · intro agrees
    funext db q
    exact agrees db (translate q) ⟨q, rfl⟩

theorem collapse_extendUB (embedding : Small ↪ Large) (reason : Reason)
    (sem : ExplicitQuery DB Small Result Reason) :
    (sem.extendUB embedding reason).collapse = sem.collapse.extendUB embedding := by
  funext db query
  change (extendQueries embedding _ sem db query).collapse =
    extendQueries embedding _ sem.collapse db query
  by_cases h : ∃ q, embedding q = query
  · obtain ⟨q, rfl⟩ := h
    rw [extendQueries_apply_image, extendQueries_apply_image]
    rfl
  · rw [extendQueries_apply_outside _ _ _ _ _ h, extendQueries_apply_outside _ _ _ _ _ h]
    exact Explicit.collapse_undefined reason

theorem forget_extendUB (embedding : Small ↪ Large) (reason : Reason)
    (sem : ExplicitQuery DB Small Result Reason) :
    (sem.extendUB embedding reason).forget = sem.forget.extend embedding := by
  funext db query result
  apply propext
  change result ∈ Explicit.forget (extendQueries embedding _ sem db query) ↔
    ∃ q, embedding q = query ∧ sem.forget db q result
  by_cases h : ∃ q, embedding q = query
  · obtain ⟨q, rfl⟩ := h
    rw [extendQueries_apply_image]
    exact ⟨fun seen => ⟨q, rfl, seen⟩,
      fun ⟨other, eq, seen⟩ => embedding.injective eq ▸ seen⟩
  · rw [extendQueries_apply_outside _ _ _ _ _ h, Explicit.forget_undefined]
    exact ⟨False.elim, fun ⟨q, eq, _⟩ => (h ⟨q, eq⟩).elim⟩

end Silmaril.Proofs.Relational.UB
