module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.RegionAt

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env env' : Env α}

theorem br (i : Nat) {a b : Tm Φ} (h : TermAt O env a env' b) :
    RegionAt O env (.br i a) env' (.br i b) where
  eval := by
    intro s label v t
    constructor
    · intro run; cases run with | br arg => exact .br (h.eval.mp arg)
    · intro run; cases run with | br arg => exact .br (h.eval.mpr arg)
  fault := by
    intro s t
    constructor
    · intro run; cases run with | br arg => exact .br (h.fault.mp arg)
    · intro run; cases run with | br arg => exact .br (h.fault.mpr arg)
  div := by
    intro s
    constructor
    · intro d; cases d.unfold with
      | core step => cases step
      | br arg => exact .fold (.br (h.div.mp arg))
    · intro d; cases d.unfold with
      | core step => cases step
      | br arg => exact .fold (.br (h.div.mpr arg))

private theorem let₁_dir {a b : Tm Φ} {r t : Region Φ}
    (head : TermAt O env a env' b)
    (body : ∀ {s v m}, Semantics.Tm.Eval O.instr env a s v m →
      RegionAt O (extend env v) r (extend env' v) t) :
    (∀ {s i v e}, Semantics.Region.Eval O.instr env (.let₁ a r) s i v e →
      Semantics.Region.Eval O.instr env' (.let₁ b t) s i v e) ∧
    (∀ {s e}, Semantics.Region.Fault O.instr O.faults env (.let₁ a r) s e →
      Semantics.Region.Fault O.instr O.faults env' (.let₁ b t) s e) ∧
    (∀ {s}, Semantics.External.Diverges O.instr O.prim (.region env (.let₁ a r) s) →
      Semantics.External.Diverges O.instr O.prim (.region env' (.let₁ b t) s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i v e run
    cases run with | let₁ arg rest => exact .let₁ (head.eval.mp arg) ((body arg).eval.mp rest)
  · intro s e run
    cases run with
    | let₁_arg arg => exact .let₁_arg (head.fault.mp arg)
    | let₁_body arg rest => exact .let₁_body (head.eval.mp arg) ((body arg).fault.mp rest)
  · intro s run
    cases run.unfold with
    | let₁_arg arg => exact .fold (.let₁_arg (head.div.mp arg))
    | core step => cases step with
      | let₁ arg rest => exact .fold_core (.let₁ (head.eval.mp arg) ((body arg).div.mp rest))

theorem let₁ {a b : Tm Φ} {r t : Region Φ}
    (head : TermAt O env a env' b)
    (body : ∀ {s v m}, Semantics.Tm.Eval O.instr env a s v m →
      RegionAt O (extend env v) r (extend env' v) t) :
    RegionAt O env (.let₁ a r) env' (.let₁ b t) := by
  have f := let₁_dir head body
  have g := let₁_dir head.symm (fun arg => (body (head.eval.mpr arg)).symm)
  exact ⟨⟨f.1, g.1⟩, ⟨f.2.1, g.2.1⟩, ⟨f.2.2, g.2.2⟩⟩

private theorem let₂_dir {a b : Tm Φ} {r t : Region Φ}
    (head : TermAt O env a env' b)
    (body : ∀ {s l r' m}, Semantics.Tm.Eval O.instr env a s (.pair l r') m →
      RegionAt O (extend (extend env l) r') r (extend (extend env' l) r') t) :
    (∀ {s i v e}, Semantics.Region.Eval O.instr env (.let₂ a r) s i v e →
      Semantics.Region.Eval O.instr env' (.let₂ b t) s i v e) ∧
    (∀ {s e}, Semantics.Region.Fault O.instr O.faults env (.let₂ a r) s e →
      Semantics.Region.Fault O.instr O.faults env' (.let₂ b t) s e) ∧
    (∀ {s}, Semantics.External.Diverges O.instr O.prim (.region env (.let₂ a r) s) →
      Semantics.External.Diverges O.instr O.prim (.region env' (.let₂ b t) s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i v e run
    cases run with | let₂ arg rest => exact .let₂ (head.eval.mp arg) ((body arg).eval.mp rest)
  · intro s e run
    cases run with
    | let₂_arg arg => exact .let₂_arg (head.fault.mp arg)
    | let₂_body arg rest => exact .let₂_body (head.eval.mp arg) ((body arg).fault.mp rest)
  · intro s run
    cases run.unfold with
    | let₂_arg arg => exact .fold (.let₂_arg (head.div.mp arg))
    | core step => cases step with
      | let₂ arg rest => exact .fold_core (.let₂ (head.eval.mp arg) ((body arg).div.mp rest))

theorem let₂ {a b : Tm Φ} {r t : Region Φ}
    (head : TermAt O env a env' b)
    (body : ∀ {s l r' m}, Semantics.Tm.Eval O.instr env a s (.pair l r') m →
      RegionAt O (extend (extend env l) r') r (extend (extend env' l) r') t) :
    RegionAt O env (.let₂ a r) env' (.let₂ b t) := by
  have f := let₂_dir head body
  have g := let₂_dir head.symm (fun arg => (body (head.eval.mpr arg)).symm)
  exact ⟨⟨f.1, g.1⟩, ⟨f.2.1, g.2.1⟩, ⟨f.2.2, g.2.2⟩⟩

private theorem case_dir {a b : Tm Φ} {l l' r r' : Region Φ}
    (head : TermAt O env a env' b)
    (left : ∀ {s v m}, Semantics.Tm.Eval O.instr env a s (.inl v) m →
      RegionAt O (extend env v) l (extend env' v) l')
    (right : ∀ {s v m}, Semantics.Tm.Eval O.instr env a s (.inr v) m →
      RegionAt O (extend env v) r (extend env' v) r') :
    (∀ {s i v e}, Semantics.Region.Eval O.instr env (.case a l r) s i v e →
      Semantics.Region.Eval O.instr env' (.case b l' r') s i v e) ∧
    (∀ {s e}, Semantics.Region.Fault O.instr O.faults env (.case a l r) s e →
      Semantics.Region.Fault O.instr O.faults env' (.case b l' r') s e) ∧
    (∀ {s}, Semantics.External.Diverges O.instr O.prim (.region env (.case a l r) s) →
      Semantics.External.Diverges O.instr O.prim (.region env' (.case b l' r') s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i v e run
    cases run with
    | case_inl arg rest => exact .case_inl (head.eval.mp arg) ((left arg).eval.mp rest)
    | case_inr arg rest => exact .case_inr (head.eval.mp arg) ((right arg).eval.mp rest)
  · intro s e run
    cases run with
    | case_arg arg => exact .case_arg (head.fault.mp arg)
    | case_inl arg rest => exact .case_inl (head.eval.mp arg) ((left arg).fault.mp rest)
    | case_inr arg rest => exact .case_inr (head.eval.mp arg) ((right arg).fault.mp rest)
  · intro s run
    cases run.unfold with
    | case_arg arg => exact .fold (.case_arg (head.div.mp arg))
    | core step => cases step with
      | case_inl arg rest => exact .fold_core (.case_inl (head.eval.mp arg) ((left arg).div.mp rest))
      | case_inr arg rest => exact .fold_core (.case_inr (head.eval.mp arg) ((right arg).div.mp rest))

theorem case {a b : Tm Φ} {l l' r r' : Region Φ}
    (head : TermAt O env a env' b)
    (left : ∀ {s v m}, Semantics.Tm.Eval O.instr env a s (.inl v) m →
      RegionAt O (extend env v) l (extend env' v) l')
    (right : ∀ {s v m}, Semantics.Tm.Eval O.instr env a s (.inr v) m →
      RegionAt O (extend env v) r (extend env' v) r') :
    RegionAt O env (.case a l r) env' (.case b l' r') := by
  have f := case_dir head left right
  have g := case_dir head.symm (fun arg => (left (head.eval.mpr arg)).symm)
    (fun arg => (right (head.eval.mpr arg)).symm)
  exact ⟨⟨f.1, g.1⟩, ⟨f.2.1, g.2.1⟩, ⟨f.2.2, g.2.2⟩⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.RegionAt
