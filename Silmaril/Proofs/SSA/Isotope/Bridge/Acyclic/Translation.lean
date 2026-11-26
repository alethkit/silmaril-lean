module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Defs

public section

universe u v w q

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Acyclic
open Silmaril.Isotope.Morphism.CaseSSA (EnvAgrees erase_caseEval_iff erase_hasType)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {n : Nat} {β : BoundCtx τ n} {A : τ}

theorem toSSA_hasType (c : Code Φ β A) {L : LCtx τ} {exit : Nat}
    (h : At L exit A) : Region.HasType β.toList (c.toSSA exit) L := by
  induction c generalizing L exit with
  | br a => exact .br h (erase_hasType a.2.toHasType)
  | let₁ a _ ih => exact .let₁ (erase_hasType a.2.toHasType) (ih h)
  | let₂ a _ ih => exact .let₂ (erase_hasType a.2.toHasType) (ih h)
  | case e _ _ ihl ihr => exact .case (erase_hasType e.2.toHasType) (ihl h) (ihr h)
  | @join _ _ B _ entry block ihe ihb =>
      let types : Fin 1 → τ := fun _ => B
      have htypes : List.ofFn types ++ L = B :: L := by simp [types, List.ofFn_succ]
      apply Region.HasType.cfg types
      · rw [htypes]
        exact ihe (exit := 0) rfl
      · intro i
        rw [htypes]
        exact ihb (exit := exit + 1) h

theorem toLetCase_ofLetCase {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : LetCase.LocallyNameless.Derivation Φ (.nil : Ctx Empty τ) β t A) :
    (Code.ofLetCase d).toLetCase = ⟨t, d⟩ := by
  induction d with
  | @fv _ _ x => exact x.elim
  | bv | op | unit | pair | inl | inr | abort => rfl
  | @let₁ _ β _ _ A B _ _ iha ihb =>
      exact congrArg₂ (fun (a : Operand Φ β A) (b : Operand Φ (β.snoc A) B) =>
        (⟨.let₁ a.1 b.1, .let₁ a.2 b.2⟩ : Operand Φ β B)) iha ihb
  | @let₂ _ β _ _ A B C ha _ _ ihb =>
      exact congrArg (fun (b : Operand Φ ((β.snoc A).snoc B) C) =>
        (⟨.let₂ _ b.1, .let₂ ha b.2⟩ : Operand Φ β C)) ihb
  | @case _ β _ _ _ A B C he _ _ _ ihl ihr =>
      exact congrArg₂ (fun (l : Operand Φ (β.snoc A) C) (r : Operand Φ (β.snoc B) C) =>
        (⟨.case _ l.1 r.1, .case he l.2 r.2⟩ : Operand Φ β C)) ihl ihr

open LambdaSSA.Semantics

theorem eval_toSSA_iff (c : Code Φ β A)
    {α : Type w} {σ : Type q} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Env α} {bound : LetCase.Semantics.BoundEnv α n}
    {s s' : σ} {value : Value α} {exit label : Nat} (agree : EnvAgrees env bound) :
    Region.Eval instr env (c.toSSA exit) s label value s' ↔
      label = exit ∧ LetCase.Semantics.Eval instr Empty.elim bound c.toLetCase.1 s value s' := by
  induction c generalizing env s s' value exit label with
  | br a =>
      simp only [Code.toSSA, Code.toLetCase]
      constructor
      · intro h
        cases h with | br arg => exact ⟨rfl, (erase_caseEval_iff agree).mp arg⟩
      · rintro ⟨rfl, arg⟩
        exact .br ((erase_caseEval_iff agree).mpr arg)
  | let₁ a _ ih =>
      simp only [Code.toSSA, Code.toLetCase]
      constructor
      · intro h
        cases h with
        | let₁ arg body =>
            obtain ⟨rfl, hb⟩ := (ih (agree.extend _)).mp body
            exact ⟨rfl, .let₁ ((erase_caseEval_iff agree).mp arg) hb⟩
      · rintro ⟨rfl, h⟩
        cases h with
        | let₁ arg body =>
            exact .let₁ ((erase_caseEval_iff agree).mpr arg)
              ((ih (agree.extend _)).mpr ⟨rfl, body⟩)
  | let₂ a _ ih =>
      simp only [Code.toSSA, Code.toLetCase]
      constructor
      · intro h
        cases h with
        | let₂ arg body =>
            obtain ⟨rfl, hb⟩ := (ih ((agree.extend _).extend _)).mp body
            exact ⟨rfl, .let₂ ((erase_caseEval_iff agree).mp arg) hb⟩
      · rintro ⟨rfl, h⟩
        cases h with
        | let₂ arg body =>
            exact .let₂ ((erase_caseEval_iff agree).mpr arg)
              ((ih ((agree.extend _).extend _)).mpr ⟨rfl, body⟩)
  | case e _ _ ihl ihr =>
      simp only [Code.toSSA, Code.toLetCase]
      constructor
      · intro h
        cases h with
        | case_inl discr arm =>
            obtain ⟨rfl, hl⟩ := (ihl (agree.extend _)).mp arm
            exact ⟨rfl, .case_inl ((erase_caseEval_iff agree).mp discr) hl⟩
        | case_inr discr arm =>
            obtain ⟨rfl, hr⟩ := (ihr (agree.extend _)).mp arm
            exact ⟨rfl, .case_inr ((erase_caseEval_iff agree).mp discr) hr⟩
      · rintro ⟨rfl, h⟩
        cases h with
        | case_inl discr arm =>
            exact .case_inl ((erase_caseEval_iff agree).mpr discr)
              ((ihl (agree.extend _)).mpr ⟨rfl, arm⟩)
        | case_inr discr arm =>
            exact .case_inr ((erase_caseEval_iff agree).mpr discr)
              ((ihr (agree.extend _)).mpr ⟨rfl, arm⟩)
  | join entry block ihe ihb =>
      simp only [Code.toSSA, Code.toLetCase]
      constructor
      · intro h
        cases h with
        | cfg he hf =>
            obtain ⟨rfl, ha⟩ := (ihe agree).mp he
            cases hf with
            | exit outside => omega
            | step _ head tail =>
                obtain ⟨rfl, hb⟩ := (ihb (agree.extend _)).mp head
                cases tail with
                | exit _ => exact ⟨Nat.add_sub_cancel _ _, .let₁ ha hb⟩
                | step inside _ _ => omega
      · rintro ⟨rfl, h⟩
        cases h with
        | let₁ he hb =>
            exact .cfg ((ihe agree).mpr ⟨rfl, he⟩)
              (.step (Nat.zero_lt_succ 0) ((ihb (agree.extend _)).mpr ⟨rfl, hb⟩)
                (.exit (Nat.zero_lt_succ _)))

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic
