module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.FollowGraph
public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt)

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x}

@[expose] def Runs (O : Ops Φ α σ) (env : Env α) (r : Region Φ) (s : σ) : Exit α σ → Prop
  | .ret j a t => Semantics.Region.Eval O.instr env r s j a t
  | .fault t => Semantics.Region.Fault O.instr O.faults env r s t
  | .diverge => External.Diverges O.instr O.prim (.region env r s)

theorem regionAt_iff {O : Ops Φ α σ} {env env' : Env α} {r t : Region Φ} :
    RegionAt O env r env' t ↔ ∀ s o, Runs O env r s o ↔ Runs O env' t s o :=
  ⟨fun h _ o => by cases o; exacts [h.eval, h.fault, h.div],
    fun h => ⟨h _ (.ret _ _ _), h _ (.fault _), h _ .diverge⟩⟩

/-- A postcontinuation receives only successful transfers. Fault and divergence
from the producer are propagated unchanged. -/
abbrev Post (α : Type w) (σ : Type x) := Jump α σ → Exit α σ → Prop

@[expose] def Post.apply (k : Post α σ) : Exit α σ → Exit α σ → Prop
  | .ret j a s, o => k ⟨j, a, s⟩ o
  | .fault t, o => o = .fault t
  | .diverge, o => o = .diverge

abbrev Sequenced (O : Ops Φ α σ) (env : Env α) (r t : Region Φ) (k : Post α σ) : Prop :=
  ∀ s o, Runs O env t s o ↔ ∃ e, Runs O env r s e ∧ k.apply e o

variable {O : Ops Φ α σ} {env : Env α} {r t l l' : Region Φ} {k : Post α σ} {a : Tm Φ}

theorem Sequenced.congr (h : Sequenced O env r t k) {j : Post α σ}
    (same : ∀ p o, k p o ↔ j p o) : Sequenced O env r t j := by
  intro s o
  rw [h]
  apply exists_congr
  intro e
  apply and_congr_right'
  cases e
  · exact same _ _
  · rfl
  · rfl

namespace Sequenced

theorem let₁ (h : ∀ v, Sequenced O (extend env v) r t k) :
    Sequenced O env (.let₁ a r) (.let₁ a t) k := by
  intro s o
  have tail {v} {m} := h v m o
  constructor
  · intro run
    have step {v m} (arg : Semantics.Tm.Eval O.instr env a s v m)
        (body : Runs O (extend env v) t m o) :
        ∃ e, Runs O env (.let₁ a r) s e ∧ k.apply e o := by
      obtain ⟨e, produced, post⟩ := tail.mp body
      refine ⟨e, ?_, post⟩
      cases e
      · exact Semantics.Region.Eval.let₁ arg produced
      · exact Semantics.Region.Fault.let₁_body arg produced
      · exact External.Diverges.fold_core (.let₁ arg produced)
    cases o with
    | ret => cases run with | let₁ arg body => exact step arg body
    | fault f =>
      cases run with
      | let₁_arg arg => exact ⟨.fault f, Semantics.Region.Fault.let₁_arg arg, rfl⟩
      | let₁_body arg body => exact step arg body
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | let₁_arg arg => exact ⟨.diverge, External.Diverges.fold (.let₁_arg arg), rfl⟩
      | core h => cases h with | let₁ arg body => exact step arg body
  · rintro ⟨e, run, post⟩
    have step {v m e} (arg : Semantics.Tm.Eval O.instr env a s v m)
        (body : Runs O (extend env v) r m e) (post : k.apply e o) :
        Runs O env (.let₁ a t) s o := by
      have done := tail.mpr ⟨e, body, post⟩
      cases o
      · exact Semantics.Region.Eval.let₁ arg done
      · exact Semantics.Region.Fault.let₁_body arg done
      · exact External.Diverges.fold_core (.let₁ arg done)
    cases e with
    | ret j v f => cases run with | let₁ arg body => exact step (e := .ret j v f) arg body post
    | fault f =>
      cases run with
      | let₁_arg arg =>
        cases (show o = .fault f from post)
        exact Semantics.Region.Fault.let₁_arg arg
      | let₁_body arg body => exact step (e := .fault f) arg body post
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | let₁_arg arg =>
        cases (show o = .diverge from post)
        exact External.Diverges.fold (.let₁_arg arg)
      | core h => cases h with | let₁ arg body => exact step (e := .diverge) arg body post

theorem let₂ (h : ∀ v w, Sequenced O (extend (extend env v) w) r t k) :
    Sequenced O env (.let₂ a r) (.let₂ a t) k := by
  intro s o
  constructor
  · intro run
    have step {v w m} (arg : Semantics.Tm.Eval O.instr env a s (.pair v w) m)
        (body : Runs O (extend (extend env v) w) t m o) :
        ∃ e, Runs O env (.let₂ a r) s e ∧ k.apply e o := by
      obtain ⟨e, produced, post⟩ := (h v w m o).mp body
      refine ⟨e, ?_, post⟩
      cases e
      · exact Semantics.Region.Eval.let₂ arg produced
      · exact Semantics.Region.Fault.let₂_body arg produced
      · exact External.Diverges.fold_core (.let₂ arg produced)
    cases o with
    | ret => cases run with | let₂ arg body => exact step arg body
    | fault f =>
      cases run with
      | let₂_arg arg => exact ⟨.fault f, Semantics.Region.Fault.let₂_arg arg, rfl⟩
      | let₂_body arg body => exact step arg body
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | let₂_arg arg => exact ⟨.diverge, External.Diverges.fold (.let₂_arg arg), rfl⟩
      | core h => cases h with | let₂ arg body => exact step arg body
  · rintro ⟨e, run, post⟩
    have step {v w m e} (arg : Semantics.Tm.Eval O.instr env a s (.pair v w) m)
        (body : Runs O (extend (extend env v) w) r m e) (post : k.apply e o) :
        Runs O env (.let₂ a t) s o := by
      have done := (h v w m o).mpr ⟨e, body, post⟩
      cases o
      · exact Semantics.Region.Eval.let₂ arg done
      · exact Semantics.Region.Fault.let₂_body arg done
      · exact External.Diverges.fold_core (.let₂ arg done)
    cases e with
    | ret j v f => cases run with | let₂ arg body => exact step (e := .ret j v f) arg body post
    | fault f =>
      cases run with
      | let₂_arg arg =>
        cases (show o = .fault f from post)
        exact Semantics.Region.Fault.let₂_arg arg
      | let₂_body arg body => exact step (e := .fault f) arg body post
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | let₂_arg arg =>
        cases (show o = .diverge from post)
        exact External.Diverges.fold (.let₂_arg arg)
      | core h => cases h with | let₂ arg body => exact step (e := .diverge) arg body post

theorem case (hl : ∀ v, Sequenced O (extend env v) l l' k)
    (hr : ∀ v, Sequenced O (extend env v) r t k) :
    Sequenced O env (.case a l r) (.case a l' t) k := by
  intro s o
  have left {v m e} (arg : Semantics.Tm.Eval O.instr env a s (.inl v) m)
      {b c : Region Φ} (run : Runs O (extend env v) b m e) :
      Runs O env (.case a b c) s e := by
    cases e
    · exact Semantics.Region.Eval.case_inl arg run
    · exact Semantics.Region.Fault.case_inl arg run
    · exact External.Diverges.fold_core (.case_inl arg run)
  have right {v m e} (arg : Semantics.Tm.Eval O.instr env a s (.inr v) m)
      {b c : Region Φ} (run : Runs O (extend env v) c m e) :
      Runs O env (.case a b c) s e := by
    cases e
    · exact Semantics.Region.Eval.case_inr arg run
    · exact Semantics.Region.Fault.case_inr arg run
    · exact External.Diverges.fold_core (.case_inr arg run)
  have fromLeft {v m} (arg : Semantics.Tm.Eval O.instr env a s (.inl v) m)
      (body : Runs O (extend env v) l' m o) : ∃ e, Runs O env (.case a l r) s e ∧ k.apply e o := by
    obtain ⟨e, run, post⟩ := (hl v m o).mp body
    exact ⟨e, left arg run, post⟩
  have fromRight {v m} (arg : Semantics.Tm.Eval O.instr env a s (.inr v) m)
      (body : Runs O (extend env v) t m o) : ∃ e, Runs O env (.case a l r) s e ∧ k.apply e o := by
    obtain ⟨e, run, post⟩ := (hr v m o).mp body
    exact ⟨e, right arg run, post⟩
  constructor
  · intro run
    cases o with
    | ret => cases run with
      | case_inl arg body => exact fromLeft arg body
      | case_inr arg body => exact fromRight arg body
    | fault f => cases run with
      | case_arg arg => exact ⟨.fault f, Semantics.Region.Fault.case_arg arg, rfl⟩
      | case_inl arg body => exact fromLeft arg body
      | case_inr arg body => exact fromRight arg body
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | case_arg arg => exact ⟨.diverge, External.Diverges.fold (.case_arg arg), rfl⟩
      | core h => cases h with
        | case_inl arg body => exact fromLeft arg body
        | case_inr arg body => exact fromRight arg body
  · rintro ⟨e, run, post⟩
    cases e with
    | ret j v f => cases run with
      | case_inl arg body => exact left arg ((hl _ _ o).mpr ⟨.ret j v f, body, post⟩)
      | case_inr arg body => exact right arg ((hr _ _ o).mpr ⟨.ret j v f, body, post⟩)
    | fault f => cases run with
      | case_arg arg =>
        cases (show o = .fault f from post)
        exact Semantics.Region.Fault.case_arg arg
      | case_inl arg body => exact left arg ((hl _ _ o).mpr ⟨.fault f, body, post⟩)
      | case_inr arg body => exact right arg ((hr _ _ o).mpr ⟨.fault f, body, post⟩)
    | diverge =>
      cases (show External.Diverges O.instr O.prim _ from run).unfold with
      | case_arg arg =>
        cases (show o = .diverge from post)
        exact External.Diverges.fold (.case_arg arg)
      | core h => cases h with
        | case_inl arg body => exact left arg ((hl _ _ o).mpr ⟨.diverge, body, post⟩)
        | case_inr arg body => exact right arg ((hr _ _ o).mpr ⟨.diverge, body, post⟩)

end Sequenced
end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent
