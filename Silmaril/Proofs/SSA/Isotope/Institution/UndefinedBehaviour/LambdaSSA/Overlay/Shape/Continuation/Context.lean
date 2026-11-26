module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Binders
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Feedback
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Preservation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.ShapedObs

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Resumption.Typing

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {α : Type w} {σ : Type x}
  {Γ L : VCtx (Ty κ)} {r t q : Region Φ}

local notation "Obs" => ShapedObs (Φ := Φ) (κ := κ) (α := α) (σ := σ)

theorem of_obs (h : Region.Obs.{u,w,x} r t) : Obs Γ r t :=
  fun _ _ _ _ _ => RegionAt.of_obs h

theorem symm (h : Obs Γ r t) : Obs Γ t r :=
  fun O types steps env shaped => (h O types steps env shaped).symm

theorem trans (h : Obs Γ r t) (k : Obs Γ t q) : Obs Γ r q :=
  fun O types steps env shaped => (h O types steps env shaped).trans (k O types steps env shaped)

theorem let₁ {a : Tm Φ} {A : Ty κ} (ha : a.HasType Γ A) (h : Obs (A :: Γ) r t) :
    Obs Γ (.let₁ a r) (.let₁ a t) := by
  intro O types steps env shaped
  exact RegionAt.let₁ (TermAt.refl a) fun run =>
    h O types steps _ (shaped.extend (term_eval_typed_at steps shaped ha run))

theorem let₂ {a : Tm Φ} {A B : Ty κ} (ha : a.HasType Γ (.product A B)) (h : Obs (B :: A :: Γ) r t) :
    Obs Γ (.let₂ a r) (.let₂ a t) := by
  intro O types steps env shaped
  apply RegionAt.let₂ (TermAt.refl a)
  intro s left right mid run
  cases term_eval_typed_at steps shaped ha run with
  | pair hl hr => exact h O types steps _ ((shaped.extend hl).extend hr)

theorem case {a : Tm Φ} {A B : Ty κ} {l l' r r' : Region Φ} (ha : a.HasType Γ (.coprod A B))
    (hl : Obs (A :: Γ) l l') (hr : Obs (B :: Γ) r r') :
    Obs Γ (.case a l r) (.case a l' r') := by
  intro O types steps env shaped
  apply RegionAt.case (TermAt.refl a)
  · intro s v mid run
    cases term_eval_typed_at steps shaped ha run with
    | inl h => exact hl O types steps _ (shaped.extend h)
  · intro s v mid run
    cases term_eval_typed_at steps shaped ha run with
    | inr h => exact hr O types steps _ (shaped.extend h)

private theorem cfg_payload {n : Nat} (R : Fin n → Ty κ)
    {O : Ops Φ α σ} {types : α → κ → Prop}
    (steps : InstrTyped types O.instr) {env : Env α} (shaped : EnvTyped types Γ env)
    {r : Region Φ} (typed : r.HasType Γ (List.ofFn R ++ L)) {s t : σ} {i : Nat} {v : Value α}
    (run : Semantics.Region.Eval O.instr env r s i v t) (hi : i < n) :
    ValueTyped types v (R ⟨i, hi⟩) := by
  obtain ⟨A, atLabel, value⟩ := region_eval_typed_at steps shaped typed run
  have same : R ⟨i, hi⟩ = A := by
    simpa [At, List.getElem?_append, hi] using atLabel
  exact same.symm ▸ value

/-- Each continuation applies at the exact type of a reached CFG payload.
The entry and every successful local step establish that invariant. -/
theorem cfg {n : Nat} (R : Fin n → Ty κ) {entry entry' : Region Φ} {blocks blocks' : Fin n → Region Φ}
    (he : entry.HasType Γ (List.ofFn R ++ L))
    (hb : ∀ i, (blocks i).HasType (R i :: Γ) (List.ofFn R ++ L))
    (entryEq : Obs Γ entry entry') (body : ∀ i, Obs (R i :: Γ) (blocks i) (blocks' i)) :
    Obs Γ (.cfg entry n blocks) (.cfg entry' n blocks') := by
  intro O types steps env shaped
  let guard (i : Nat) (v : Value α) := ∀ hi : i < n, ValueTyped types v (R ⟨i, hi⟩)
  apply RegionAt.cfg (guard := guard) (entryEq O types steps env shaped)
  · exact cfg_payload R steps shaped he
  · intro i v typed
    exact body i O types steps _ (shaped.extend (typed i.isLt))
  · intro i v s j w t typed run
    exact cfg_payload R steps (shaped.extend (typed i.isLt)) (hb i) run

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.ShapedObs
