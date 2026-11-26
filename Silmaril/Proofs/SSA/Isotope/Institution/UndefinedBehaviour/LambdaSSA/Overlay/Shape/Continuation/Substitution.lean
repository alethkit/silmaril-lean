module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Values
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Binders
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Feedback

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x}
  {O : Ops Φ α σ} {env source : Env α} {θ : Nat → Tm Φ}

theorem Realizes.term (h : Realizes O env θ source) (a : Tm Φ) :
    TermAt O env (a.subst θ) source a := by
  induction a generalizing env source θ with
  | var i => exact (h i).same (.var i)
  | unit => exact (PureValue.unit (env := env)).same PureValue.unit
  | op f a ih =>
    simp only [Tm.subst]
    have arg := ih h
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor
      · intro run; cases run with | op e hop => exact .op (arg.eval.mp e) hop
      · intro run; cases run with | op e hop => exact .op (arg.eval.mpr e) hop
    · intro s t
      constructor
      · intro run
        cases run with
        | op_arg e => exact .op_arg (arg.fault.mp e)
        | op_fault e hop => exact .op_fault (arg.eval.mp e) hop
      · intro run
        cases run with
        | op_arg e => exact .op_arg (arg.fault.mpr e)
        | op_fault e hop => exact .op_fault (arg.eval.mpr e) hop
    · intro s
      constructor
      · intro run
        cases run with
        | op_arg e => exact .op_arg (arg.div.mp e)
        | primitive e hop => exact .primitive (arg.eval.mp e) hop
      · intro run
        cases run with
        | op_arg e => exact .op_arg (arg.div.mpr e)
        | primitive e hop => exact .primitive (arg.eval.mpr e) hop
  | pair a b ia ib =>
    simp only [Tm.subst]
    have left := ia h
    have right := ib h
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor
      · intro run; cases run with | pair a b => exact .pair (left.eval.mp a) (right.eval.mp b)
      · intro run; cases run with | pair a b => exact .pair (left.eval.mpr a) (right.eval.mpr b)
    · intro s t
      constructor
      · intro run
        cases run with
        | pair_left a => exact .pair_left (left.fault.mp a)
        | pair_right a b => exact .pair_right (left.eval.mp a) (right.fault.mp b)
      · intro run
        cases run with
        | pair_left a => exact .pair_left (left.fault.mpr a)
        | pair_right a b => exact .pair_right (left.eval.mpr a) (right.fault.mpr b)
    · intro s
      constructor
      · intro run
        cases run with
        | pair_left a => exact .pair_left (left.div.mp a)
        | pair_right a b => exact .pair_right (left.eval.mp a) (right.div.mp b)
      · intro run
        cases run with
        | pair_left a => exact .pair_left (left.div.mpr a)
        | pair_right a b => exact .pair_right (left.eval.mpr a) (right.div.mpr b)
  | let₁ a b ia ib =>
    simp only [Tm.subst]
    have arg := ia h
    have body v := ib (h.lift v)
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor
      · intro run; cases run with | let₁ a b => exact .let₁ (arg.eval.mp a) ((body _).eval.mp b)
      · intro run; cases run with | let₁ a b => exact .let₁ (arg.eval.mpr a) ((body _).eval.mpr b)
    · intro s t
      constructor
      · intro run
        cases run with
        | let₁_arg a => exact .let₁_arg (arg.fault.mp a)
        | let₁_body a b => exact .let₁_body (arg.eval.mp a) ((body _).fault.mp b)
      · intro run
        cases run with
        | let₁_arg a => exact .let₁_arg (arg.fault.mpr a)
        | let₁_body a b => exact .let₁_body (arg.eval.mpr a) ((body _).fault.mpr b)
    · intro s
      constructor
      · intro run
        cases run with
        | let₁_arg a => exact .let₁_arg (arg.div.mp a)
        | let₁_body a b => exact .let₁_body (arg.eval.mp a) ((body _).div.mp b)
      · intro run
        cases run with
        | let₁_arg a => exact .let₁_arg (arg.div.mpr a)
        | let₁_body a b => exact .let₁_body (arg.eval.mpr a) ((body _).div.mpr b)
  | let₂ a b ia ib =>
    simp only [Tm.subst, Tm.liftSubstN]
    have arg := ia h
    have body l r := ib ((h.lift l).lift r)
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor
      · intro run; cases run with | let₂ a b => exact .let₂ (arg.eval.mp a) ((body _ _).eval.mp b)
      · intro run; cases run with | let₂ a b => exact .let₂ (arg.eval.mpr a) ((body _ _).eval.mpr b)
    · intro s t
      constructor
      · intro run
        cases run with
        | let₂_arg a => exact .let₂_arg (arg.fault.mp a)
        | let₂_body a b => exact .let₂_body (arg.eval.mp a) ((body _ _).fault.mp b)
      · intro run
        cases run with
        | let₂_arg a => exact .let₂_arg (arg.fault.mpr a)
        | let₂_body a b => exact .let₂_body (arg.eval.mpr a) ((body _ _).fault.mpr b)
    · intro s
      constructor
      · intro run
        cases run with
        | let₂_arg a => exact .let₂_arg (arg.div.mp a)
        | let₂_body a b => exact .let₂_body (arg.eval.mp a) ((body _ _).div.mp b)
      · intro run
        cases run with
        | let₂_arg a => exact .let₂_arg (arg.div.mpr a)
        | let₂_body a b => exact .let₂_body (arg.eval.mpr a) ((body _ _).div.mpr b)
  | inl a ih =>
    simp only [Tm.subst]
    have arg := ih h
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor
      · intro run; cases run with | inl e => exact .inl (arg.eval.mp e)
      · intro run; cases run with | inl e => exact .inl (arg.eval.mpr e)
    · intro s t
      constructor
      · intro run; cases run with | inl e => exact .inl (arg.fault.mp e)
      · intro run; cases run with | inl e => exact .inl (arg.fault.mpr e)
    · intro s
      constructor
      · intro run; cases run with | inl e => exact .inl (arg.div.mp e)
      · intro run; cases run with | inl e => exact .inl (arg.div.mpr e)
  | inr a ih =>
    simp only [Tm.subst]
    have arg := ih h
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor
      · intro run; cases run with | inr e => exact .inr (arg.eval.mp e)
      · intro run; cases run with | inr e => exact .inr (arg.eval.mpr e)
    · intro s t
      constructor
      · intro run; cases run with | inr e => exact .inr (arg.fault.mp e)
      · intro run; cases run with | inr e => exact .inr (arg.fault.mpr e)
    · intro s
      constructor
      · intro run; cases run with | inr e => exact .inr (arg.div.mp e)
      · intro run; cases run with | inr e => exact .inr (arg.div.mpr e)
  | case a l r ia il ir =>
    simp only [Tm.subst]
    have arg := ia h
    have left v := il (h.lift v)
    have right v := ir (h.lift v)
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor
      · intro run
        cases run with
        | case_inl e rest => exact .case_inl (arg.eval.mp e) ((left _).eval.mp rest)
        | case_inr e rest => exact .case_inr (arg.eval.mp e) ((right _).eval.mp rest)
      · intro run
        cases run with
        | case_inl e rest => exact .case_inl (arg.eval.mpr e) ((left _).eval.mpr rest)
        | case_inr e rest => exact .case_inr (arg.eval.mpr e) ((right _).eval.mpr rest)
    · intro s t
      constructor
      · intro run
        cases run with
        | case_arg e => exact .case_arg (arg.fault.mp e)
        | case_inl e rest => exact .case_inl (arg.eval.mp e) ((left _).fault.mp rest)
        | case_inr e rest => exact .case_inr (arg.eval.mp e) ((right _).fault.mp rest)
      · intro run
        cases run with
        | case_arg e => exact .case_arg (arg.fault.mpr e)
        | case_inl e rest => exact .case_inl (arg.eval.mpr e) ((left _).fault.mpr rest)
        | case_inr e rest => exact .case_inr (arg.eval.mpr e) ((right _).fault.mpr rest)
    · intro s
      constructor
      · intro run
        cases run with
        | case_arg e => exact .case_arg (arg.div.mp e)
        | case_inl e rest => exact .case_inl (arg.eval.mp e) ((left _).div.mp rest)
        | case_inr e rest => exact .case_inr (arg.eval.mp e) ((right _).div.mp rest)
      · intro run
        cases run with
        | case_arg e => exact .case_arg (arg.div.mpr e)
        | case_inl e rest => exact .case_inl (arg.eval.mpr e) ((left _).div.mpr rest)
        | case_inr e rest => exact .case_inr (arg.eval.mpr e) ((right _).div.mpr rest)
  | abort a ih =>
    simp only [Tm.subst]
    have arg := ih h
    refine ⟨?_, ?_, ?_⟩
    · intro s v t
      constructor <;> intro impossible <;> cases impossible
    · intro s t
      constructor
      · intro run; cases run with | abort_arg e => exact .abort_arg (arg.fault.mp e)
      · intro run; cases run with | abort_arg e => exact .abort_arg (arg.fault.mpr e)
    · intro s
      constructor
      · intro run; cases run with | abort_arg e => exact .abort_arg (arg.div.mp e)
      · intro run; cases run with | abort_arg e => exact .abort_arg (arg.div.mpr e)

theorem Realizes.region (h : Realizes O env θ source) (r : Region Φ) :
    RegionAt O env (r.substVars θ) source r := by
  induction r generalizing env source θ with
  | br i a => exact .br i (h.term a)
  | let₁ a r ih => exact .let₁ (h.term a) (fun _ => ih (h.lift _))
  | let₂ a r ih => exact .let₂ (h.term a) (fun _ => ih ((h.lift _).lift _))
  | case a l r il ir => exact .case (h.term a) (fun _ => il (h.lift _)) (fun _ => ir (h.lift _))
  | cfg e n blocks ie ib =>
    exact RegionAt.cfg (guard := fun _ _ => True) (ie h) (fun _ => trivial)
      (fun i v _ => ib i (h.lift v)) (fun _ _ => trivial)

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
