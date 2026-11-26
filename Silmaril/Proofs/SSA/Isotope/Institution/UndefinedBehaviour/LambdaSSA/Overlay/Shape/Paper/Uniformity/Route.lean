module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops)

universe u w x

abbrev Route (α : Type w) (σ : Type x) := Nat → Value α → σ → Nat → Value α → Prop

/-- The protected prefix retains both the original label and its payload. -/
@[expose] def Route.under {α : Type w} {σ : Type x} (n : Nat) (route : Route α σ) : Route α σ :=
  fun i a s j b =>
    if i < n then j = i ∧ b = a else ∃ k, j = n + k ∧ route (i - n) a s k b

variable {Φ : Type u} {α : Type w} {σ : Type x}

structure Routed (O : Ops Φ α σ) (env : Env α) (r t : Region Φ) (route : Route α σ) : Prop where
  eval : ∀ {s j b t'}, Semantics.Region.Eval O.instr env t s j b t' ↔
    ∃ i a, Semantics.Region.Eval O.instr env r s i a t' ∧ route i a t' j b
  fault : ∀ {s t'}, Semantics.Region.Fault O.instr O.faults env t s t' ↔
    Semantics.Region.Fault O.instr O.faults env r s t'
  div : ∀ {s}, External.Diverges O.instr O.prim (.region env t s) ↔
    External.Diverges O.instr O.prim (.region env r s)

namespace Routed

variable {O : Ops Φ α σ} {env : Env α} {route : Route α σ}
  {r t l l' : Region Φ} {a : Tm Φ}

theorem congr_route {route' : Route α σ} (h : Routed O env r t route)
    (same : ∀ i a s j b, route i a s j b ↔ route' i a s j b) : Routed O env r t route' where
  eval := by intro s j b t'; simp only [h.eval, same]
  fault := h.fault
  div := h.div

theorem let₁ (body : ∀ v, Routed O (extend env v) r t route) :
    Routed O env (.let₁ a r) (.let₁ a t) route where
  eval := by
    intro s j v t
    constructor
    · intro h; cases h with
      | let₁ head tail =>
        obtain ⟨i, b, tail, map⟩ := (body _).eval.mp tail
        exact ⟨i, b, .let₁ head tail, map⟩
    · rintro ⟨i, b, run, map⟩
      cases run with
      | let₁ head tail => exact .let₁ head ((body _).eval.mpr ⟨i, b, tail, map⟩)
  fault := by
    intro s t
    constructor
    · intro h; cases h with
      | let₁_arg h => exact .let₁_arg h
      | let₁_body head tail => exact .let₁_body head ((body _).fault.mp tail)
    · intro h; cases h with
      | let₁_arg h => exact .let₁_arg h
      | let₁_body head tail => exact .let₁_body head ((body _).fault.mpr tail)
  div := by
    intro s
    constructor
    · intro h; cases h.unfold with
      | let₁_arg h => exact .fold (.let₁_arg h)
      | core h => cases h with
        | let₁ head tail => exact .fold_core (.let₁ head ((body _).div.mp tail))
    · intro h; cases h.unfold with
      | let₁_arg h => exact .fold (.let₁_arg h)
      | core h => cases h with
        | let₁ head tail => exact .fold_core (.let₁ head ((body _).div.mpr tail))

theorem let₂ (body : ∀ l r', Routed O (extend (extend env l) r') r t route) :
    Routed O env (.let₂ a r) (.let₂ a t) route where
  eval := by
    intro s j v t
    constructor
    · intro h; cases h with
      | let₂ head tail =>
        obtain ⟨i, b, tail, map⟩ := (body _ _).eval.mp tail
        exact ⟨i, b, .let₂ head tail, map⟩
    · rintro ⟨i, b, run, map⟩
      cases run with
      | let₂ head tail => exact .let₂ head ((body _ _).eval.mpr ⟨i, b, tail, map⟩)
  fault := by
    intro s t
    constructor
    · intro h; cases h with
      | let₂_arg h => exact .let₂_arg h
      | let₂_body head tail => exact .let₂_body head ((body _ _).fault.mp tail)
    · intro h; cases h with
      | let₂_arg h => exact .let₂_arg h
      | let₂_body head tail => exact .let₂_body head ((body _ _).fault.mpr tail)
  div := by
    intro s
    constructor
    · intro h; cases h.unfold with
      | let₂_arg h => exact .fold (.let₂_arg h)
      | core h => cases h with
        | let₂ head tail => exact .fold_core (.let₂ head ((body _ _).div.mp tail))
    · intro h; cases h.unfold with
      | let₂_arg h => exact .fold (.let₂_arg h)
      | core h => cases h with
        | let₂ head tail => exact .fold_core (.let₂ head ((body _ _).div.mpr tail))

theorem case (left : ∀ v, Routed O (extend env v) l l' route)
    (right : ∀ v, Routed O (extend env v) r t route) :
    Routed O env (.case a l r) (.case a l' t) route where
  eval := by
    intro s j v t
    constructor
    · intro h; cases h with
      | case_inl head tail =>
        obtain ⟨i, b, tail, map⟩ := (left _).eval.mp tail
        exact ⟨i, b, .case_inl head tail, map⟩
      | case_inr head tail =>
        obtain ⟨i, b, tail, map⟩ := (right _).eval.mp tail
        exact ⟨i, b, .case_inr head tail, map⟩
    · rintro ⟨i, b, run, map⟩
      cases run with
      | case_inl head tail => exact .case_inl head ((left _).eval.mpr ⟨i, b, tail, map⟩)
      | case_inr head tail => exact .case_inr head ((right _).eval.mpr ⟨i, b, tail, map⟩)
  fault := by
    intro s t
    constructor
    · intro h; cases h with
      | case_arg h => exact .case_arg h
      | case_inl head tail => exact .case_inl head ((left _).fault.mp tail)
      | case_inr head tail => exact .case_inr head ((right _).fault.mp tail)
    · intro h; cases h with
      | case_arg h => exact .case_arg h
      | case_inl head tail => exact .case_inl head ((left _).fault.mpr tail)
      | case_inr head tail => exact .case_inr head ((right _).fault.mpr tail)
  div := by
    intro s
    constructor
    · intro h; cases h.unfold with
      | case_arg h => exact .fold (.case_arg h)
      | core h => cases h with
        | case_inl head tail => exact .fold_core (.case_inl head ((left _).div.mp tail))
        | case_inr head tail => exact .fold_core (.case_inr head ((right _).div.mp tail))
    · intro h; cases h.unfold with
      | case_arg h => exact .fold (.case_arg h)
      | core h => cases h with
        | case_inl head tail => exact .fold_core (.case_inl head ((left _).div.mpr tail))
        | case_inr head tail => exact .fold_core (.case_inr head ((right _).div.mpr tail))

end Routed

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity
