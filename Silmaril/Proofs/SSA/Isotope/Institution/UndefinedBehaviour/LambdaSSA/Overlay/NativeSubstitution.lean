module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Defs

import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Composition

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L K : List τ}
  (r : UB.Typed (Φ := Φ) Γ L)
  (k : (i : Fin L.length) → UB.Typed (Φ := Φ) (L.get i :: Γ) K)

theorem nativeLsubst_hasType : (nativeLsubst r k).HasType Γ K := by
  refine LambdaSSA.Region.HasType.cfg (fun i : Fin L.length => L.get i) ?_ ?_
  · rw [show List.ofFn (fun i : Fin L.length => L.get i) = L from List.ofFn_get L]
    have ren : Ren L (L ++ K) id := by
      intro i A hi
      exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1).trans hi
    simpa only [LambdaSSA.Region.renameLabels_id] using r.property.renameLabels ren
  · intro i
    rw [show List.ofFn (fun i : Fin L.length => L.get i) = L from List.ofFn_get L]
    apply (k i).property.renameLabels
    intro j A hj
    rwa [At, List.getElem?_append_right (Nat.le_add_right L.length j), Nat.add_sub_cancel_left]

section Operational

variable {α : Type w} {σ : Type x}
  {instr : Φ → Value α → σ → Value α → σ → Prop}
  {faults : Φ → Value α → σ → σ → Prop} {prim : Φ → Value α → σ → Prop}
  {env : Env α} {s s' : σ}

private theorem nativeLsubst_eval_iff {label : Nat} {value : Value α} :
    Semantics.Region.Eval instr env (nativeLsubst r k) s label value s' ↔
      ∃ (i : Fin L.length) (a : Value α) (mid : σ), Semantics.Region.Eval instr env r.val s i a mid ∧
        Semantics.Region.Eval instr (extend env a) (k i).val mid label value s' := by
  constructor
  · intro run
    change Semantics.Region.Eval instr env (.cfg r.val L.length _) s label value s' at run
    cases run with
    | cfg entry tail =>
      have inside := r.property.scoped.eval_label_lt entry
      cases tail with
      | exit outside => omega
      | step hi head after =>
        obtain ⟨j, hj, unshifted⟩ := Semantics.Region.Eval.of_renameLabels head
        subst hj
        cases after with
        | exit outside => simpa using ⟨⟨_, hi⟩, _, _, entry, unshifted⟩
        | step hi' _ _ => omega
  · rintro ⟨i, a, mid, entry, head⟩
    apply Semantics.Region.Eval.cfg entry
    apply Semantics.Region.Follow.step i.isLt (head.renameLabels (L.length + ·))
    simpa only [Nat.add_sub_cancel_left] using
      (Semantics.Region.Follow.exit (instr := instr) (env := env)
        (blocks := fun i => (k i).val.renameLabels (L.length + ·))
        (value := value) (s := s') (Nat.le_add_right L.length label))

private theorem nativeLsubst_fault_iff :
    Semantics.Region.Fault instr faults env (nativeLsubst r k) s s' ↔
      Semantics.Region.Fault instr faults env r.val s s' ∨
        ∃ (i : Fin L.length) (a : Value α) (mid : σ), Semantics.Region.Eval instr env r.val s i a mid ∧
          Semantics.Region.Fault instr faults (extend env a) (k i).val mid s' := by
  constructor
  · intro fault
    change Semantics.Region.Fault instr faults env (.cfg r.val L.length _) s s' at fault
    cases fault with
    | cfg_entry entry => exact Or.inl entry
    | cfg_follow entry tail =>
      cases tail with
      | body hi fault => exact Or.inr ⟨⟨_, hi⟩, _, _, entry, fault.of_renameLabels⟩
      | step _ run tail =>
        obtain ⟨_, hj, _⟩ := Semantics.Region.Eval.of_renameLabels run
        cases tail <;> omega
  · rintro (entry | ⟨i, a, mid, entry, fault⟩)
    · exact .cfg_entry entry
    · exact .cfg_follow entry (.body i.isLt (fault.renameLabels (L.length + ·)))

private theorem nativeLsubst_diverges_iff :
    External.Diverges instr prim (.region env (nativeLsubst r k) s) ↔
      External.Diverges instr prim (.region env r.val s) ∨
        ∃ (i : Fin L.length) (a : Value α) (mid : σ), Semantics.Region.Eval instr env r.val s i a mid ∧
          External.Diverges instr prim (.region (extend env a) (k i).val mid) := by
  constructor
  · intro div
    change External.Diverges instr prim (.region env (.cfg r.val L.length _) s) at div
    cases div.unfold with
    | core h =>
      cases h with
      | cfg_entry entry => exact Or.inl entry
      | cfg_follow entry tail =>
        cases tail.unfold with
        | core step =>
          cases step with
          | follow_body hi body =>
            exact Or.inr ⟨⟨_, hi⟩, _, _, entry,
              (External.Diverges.renameLabels_iff (L.length + ·)).mp body⟩
          | follow_next _ head tail =>
            obtain ⟨_, hj, _⟩ := Semantics.Region.Eval.of_renameLabels head
            cases tail.unfold with
            | core step => cases step <;> omega
  · rintro (entry | ⟨i, a, mid, entry, div⟩)
    · exact External.Diverges.fold_core (.cfg_entry entry)
    · exact External.Diverges.fold_core (.cfg_follow entry
        (External.Diverges.fold_core (.follow_body i.isLt
          ((External.Diverges.renameLabels_iff (L.length + ·)).mpr div))))

end Operational

theorem mem_nativeOutcomes {Δ H : List τ} (t : UB.Typed (Φ := Φ) Δ H)
    {M : Model.{u,w,x} Φ Δ.length} {env : Env M.α}
    (agree : Morphism.CaseSSA.EnvAgrees env M.bound) (s : M.σ) (o : Outcome H.length M.α M.σ) :
    o ∈ nativeOutcomes t M s ↔
      match o with
      | .ret i a s' => Semantics.Region.Eval M.instr env t.val s i a s'
      | .fault s' => Semantics.Region.Fault M.instr M.faults env t.val s s'
      | .diverge => External.Diverges M.instr M.prim (.region env t.val s) := by
  cases o with
  | ret i a s' =>
    exact scoped_eval_congr t.property.scoped (envOfBound_agrees M.bound) agree
  | fault s' =>
    exact scoped_fault_congr t.property.scoped (envOfBound_agrees M.bound) agree
  | diverge =>
    exact scoped_diverges_congr t.property.scoped (envOfBound_agrees M.bound) agree

theorem denote_native_lsubst (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    denote (.lsubst (.native r) (fun i => .native (k i))) M s =
      denote (.native ⟨nativeLsubst r k, nativeLsubst_hasType r k⟩) M s := by
  change Behaviour.bind (m := K.length) (WithTop.some (nativeOutcomes r M s))
    (fun i a mid => WithTop.some (nativeOutcomes (k i) (extendModel M a) mid)) =
      WithTop.some (nativeOutcomes ⟨nativeLsubst r k, nativeLsubst_hasType r k⟩ M s)
  rw [coe_bind]
  apply congrArg WithTop.some
  ext o
  have source := mem_nativeOutcomes r (M := M) (envOfBound_agrees M.bound)
  have targets (i : Fin L.length) (a : Value M.α) :=
    mem_nativeOutcomes (k i) (M := extendModel M a) ((envOfBound_agrees M.bound).extend a)
  rw [mem_nativeOutcomes ⟨nativeLsubst r k, nativeLsubst_hasType r k⟩ (envOfBound_agrees M.bound)]
  cases o with
  | ret i a s' =>
    simp only [Outcome.bind, Set.mem_ofPred_eq, false_or, source, targets, nativeLsubst_eval_iff]
  | fault s' =>
    simp only [Outcome.bind, Set.mem_ofPred_eq, source, targets, nativeLsubst_fault_iff]
  | diverge =>
    simp only [Outcome.bind, Set.mem_ofPred_eq, source, targets, nativeLsubst_diverges_iff]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay
