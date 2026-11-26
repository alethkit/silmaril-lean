module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Observation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.RegionAt

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x} {O : Ops Φ α σ} {env env' : Env α}
  {n : Nat} {blocks blocks' : Fin n → Region Φ} {guard : Nat → Value α → Prop}

private theorem follow_eval
    (body : ∀ (i : Fin n) v, guard i v → RegionAt O (extend env v) (blocks i) (extend env' v) (blocks' i))
    (closed : ∀ {i : Fin n} {a s j b t}, guard i a →
      Semantics.Region.Eval O.instr (extend env a) (blocks i) s j b t → guard j b)
    {i j : Nat} {a b : Value α} {s t : σ}
    (run : Semantics.Region.Follow O.instr env blocks i a s j b t) (typed : guard i a) :
    Semantics.Region.Follow O.instr env' blocks' i a s j b t := by
  induction run using Semantics.Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | exit outside => exact .exit outside
  | step inside head _ _ ih =>
    exact .step inside ((body ⟨_, inside⟩ _ typed).eval.mp head) (ih body closed (closed typed head))
  | _ => trivial

private theorem follow_fault
    (body : ∀ (i : Fin n) v, guard i v → RegionAt O (extend env v) (blocks i) (extend env' v) (blocks' i))
    (closed : ∀ {i : Fin n} {a s j b t}, guard i a →
      Semantics.Region.Eval O.instr (extend env a) (blocks i) s j b t → guard j b)
    {i : Nat} {a : Value α} {s t : σ}
    (run : Semantics.Region.FollowFault O.instr O.faults env blocks i a s t) (typed : guard i a) :
    Semantics.Region.FollowFault O.instr O.faults env' blocks' i a s t := by
  induction run using Semantics.Region.FollowFault.rec
      (motive_1 := fun _ _ _ _ _ => True) with
  | body inside fault _ => exact .body inside ((body ⟨_, inside⟩ _ typed).fault.mp fault)
  | step inside head _ ih =>
    exact .step inside ((body ⟨_, inside⟩ _ typed).eval.mp head) (ih body closed (closed typed head))
  | _ => trivial

private theorem follow_div
    (body : ∀ (i : Fin n) v, guard i v → RegionAt O (extend env v) (blocks i) (extend env' v) (blocks' i))
    (closed : ∀ {i : Fin n} {a s j b t}, guard i a →
      Semantics.Region.Eval O.instr (extend env a) (blocks i) s j b t → guard j b)
    {i : Nat} {a : Value α} {s : σ}
    (run : External.Diverges O.instr O.prim (.follow env blocks i a s)) (typed : guard i a) :
    External.Diverges O.instr O.prim (.follow env' blocks' i a s) := by
  refine External.Diverges.coinduct
    (fun c => (∃ j b t, c = .follow env' blocks' j b t ∧ guard j b ∧
      External.Diverges O.instr O.prim (.follow env blocks j b t)) ∨
      External.Diverges O.instr O.prim c) ?_ (Or.inl ⟨i, a, s, rfl, typed, run⟩)
  rintro c (⟨j, b, t, rfl, hb, div⟩ | div)
  · cases div.unfold with
    | core step =>
      cases step with
      | follow_body inside rest =>
        exact .core (.follow_body inside (Or.inr ((body ⟨_, inside⟩ _ hb).div.mp rest)))
      | follow_next inside head rest =>
        exact .core (.follow_next inside ((body ⟨_, inside⟩ _ hb).eval.mp head)
          (Or.inl ⟨_, _, _, rfl, closed hb head, rest⟩))
  · exact div.unfold.mono (fun _ => Or.inr)

private theorem cfg_dir {entry entry' : Region Φ}
    (entryEq : RegionAt O env entry env' entry')
    (entryTyped : ∀ {s i v t}, Semantics.Region.Eval O.instr env entry s i v t → guard i v)
    (body : ∀ (i : Fin n) v, guard i v → RegionAt O (extend env v) (blocks i) (extend env' v) (blocks' i))
    (closed : ∀ {i : Fin n} {a s j b t}, guard i a →
      Semantics.Region.Eval O.instr (extend env a) (blocks i) s j b t → guard j b) :
    (∀ {s i v t}, Semantics.Region.Eval O.instr env (.cfg entry n blocks) s i v t →
      Semantics.Region.Eval O.instr env' (.cfg entry' n blocks') s i v t) ∧
    (∀ {s t}, Semantics.Region.Fault O.instr O.faults env (.cfg entry n blocks) s t →
      Semantics.Region.Fault O.instr O.faults env' (.cfg entry' n blocks') s t) ∧
    (∀ {s}, External.Diverges O.instr O.prim (.region env (.cfg entry n blocks) s) →
      External.Diverges O.instr O.prim (.region env' (.cfg entry' n blocks') s)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i v t run
    cases run with
    | cfg head tail => exact .cfg (entryEq.eval.mp head) (follow_eval body closed tail (entryTyped head))
  · intro s t run
    cases run with
    | cfg_entry fault => exact .cfg_entry (entryEq.fault.mp fault)
    | cfg_follow head tail =>
      exact .cfg_follow (entryEq.eval.mp head) (follow_fault body closed tail (entryTyped head))
  · intro s run
    cases run.unfold with
    | core step => cases step with
      | cfg_entry div => exact .fold_core (.cfg_entry (entryEq.div.mp div))
      | cfg_follow head tail =>
        exact .fold_core (.cfg_follow (entryEq.eval.mp head) (follow_div body closed tail (entryTyped head)))

/-- Pointwise equality is needed only at payloads reached by successful entry
or block steps. The invariant is carried across each step of an infinite replay. -/
theorem cfg {entry entry' : Region Φ}
    (entryEq : RegionAt O env entry env' entry')
    (entryTyped : ∀ {s i v t}, Semantics.Region.Eval O.instr env entry s i v t → guard i v)
    (body : ∀ (i : Fin n) v, guard i v → RegionAt O (extend env v) (blocks i) (extend env' v) (blocks' i))
    (closed : ∀ {i : Fin n} {a s j b t}, guard i a →
      Semantics.Region.Eval O.instr (extend env a) (blocks i) s j b t → guard j b) :
    RegionAt O env (.cfg entry n blocks) env' (.cfg entry' n blocks') := by
  have f := cfg_dir entryEq entryTyped body closed
  have g := cfg_dir entryEq.symm (fun h => entryTyped (entryEq.eval.mpr h))
    (fun i a h => (body i a h).symm) (fun hi run => closed hi ((body _ _ hi).eval.mpr run))
  exact ⟨⟨f.1, g.1⟩, ⟨f.2.1, g.2.1⟩, ⟨f.2.2, g.2.2⟩⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.RegionAt
