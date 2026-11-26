module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionRouting

/-! # Complete finite runs of the packed flat CFG -/

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope.LambdaSSA.Region
open SyntacticCategory (iterationBody iterationDispatch)
open Semantics (extend Env)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}
  {α : Type w} {σ : Type x} {instr : Φ → Value α → σ → Value α → σ → Prop}

local notation "Eval" => Semantics.Region.Eval
local notation "Follow" => Semantics.Region.Follow

private theorem dispatcherBody_at (hg : FiniteCFG.HasType .nil R E g)
    {i : Nat} (hi : i < blocks)
    {env : Env α} {v out : Value α} {s t : σ} {label : Nat} :
    Eval instr (extend env (packedExitValue i v))
        (iterationBody (packedDispatcherRegion hg)) s label out t ↔
      Eval instr (extend env v) (iterationBody (routedFlat blocks (g.block ⟨i, hi⟩)))
        s label out t := by
  let body := compLSubst (blockFamily hg).val (routeFamily (List.ofFn R) (List.ofFn E)).val
  let ret : Nat → Region Φ := fun _ => iterationDispatch
  have shift : liftLSubstVars ret = ret := rfl
  have assoc : compLSubst (liftLSubstVars body) ret = liftLSubstVars (compLSubst body ret) :=
    (congrArg (compLSubst (liftLSubstVars body)) shift).symm.trans (compLSubst_liftVars body ret)
  change Eval instr _ (((unpackExits (List.ofFn R)).lsubst (liftLSubstVars body)).lsubst ret)
    s label out t ↔ _
  rw [lsubst_comp, assoc]
  change Eval instr _ (compLSubst (fun _ => unpackExits (List.ofFn R)) (compLSubst body ret) 0)
    s label out t ↔ _
  rw [unpackExits_comp_eval (List.ofFn R) (i := i) (by simpa using hi)]
  simp only [iterationBody, body, compLSubst, routeFamily, List.length_ofFn, blockFamily,
    ContinuationFamily.ofTyped, dite_eq_left hi, liftLSubstVars_routeExit, shift, routedFlat, ret]

private theorem follow_pack (hg : FiniteCFG.HasType .nil R E g)
    {env : Env α} {n i j : Nat} {bs : Fin n → Region Φ} {input output : Value α} {s t : σ}
    (h : Follow instr env bs i input s j output t) :
    ∀ (hn : n = blocks), (∀ b, bs b = (g.block (Fin.cast hn b)).erase) →
      Follow instr env (fun _ : Fin 1 => iterationBody (packedDispatcherRegion hg))
        (feedbackLabel blocks i) (feedbackPayload blocks i input) s 0 (packedExitValue j output) t := by
  induction h using Semantics.Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | @exit env n label bs value start outside =>
    intro hn _
    subst n
    simpa only [feedbackLabel, feedbackPayload, ite_eq_right (Nat.not_lt_of_ge outside)] using
      (Semantics.Region.Follow.exit (instr := instr) (env := env)
        (blocks := fun _ : Fin 1 => iterationBody (packedDispatcherRegion hg))
        (label := 1) (value := packedExitValue (label - blocks) value) (s := start)
        (by decide : 1 ≤ 1))
  | @step env n label next out bs current middle value start mid finish inside head _ _ tail =>
    intro hn hb
    subst n
    rw [hb] at head
    simp only [feedbackLabel, feedbackPayload, ite_eq_left inside]
    exact .step (by decide : 0 < 1) ((dispatcherBody_at hg inside).mpr
      ((routedFlat_body_eval _ _).mpr ⟨_, _, head, rfl, rfl⟩)) (tail rfl hb)
  | _ => trivial

private theorem follow_unpack (hg : FiniteCFG.HasType .nil R E g)
    {env : Env α} {n a j : Nat} {bs : Fin n → Region Φ} {input output : Value α} {s t : σ}
    (h : Follow instr env bs a input s j output t) :
    ∀ (_ : n = 1), (∀ b, bs b = iterationBody (packedDispatcherRegion hg)) →
      ∀ {i v}, a = feedbackLabel blocks i → input = feedbackPayload blocks i v →
        ∃ e w, Follow instr env (fun b => (g.block b).erase) i v s e w t ∧
          j = 0 ∧ output = packedExitValue e w := by
  induction h using Semantics.Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | @exit env n label bs value start outside =>
    intro hn _ i v ha hv
    subst n
    rw [ha] at outside
    have hge : blocks ≤ i := by
      by_contra! hi
      simp [feedbackLabel, hi] at outside
    simp only [feedbackLabel, feedbackPayload, ite_eq_right (Nat.not_lt_of_ge hge)] at ha hv
    exact ⟨i - blocks, v, .exit hge, by simp [ha], hv⟩
  | @step env n label next out bs current middle value start mid finish inside head _ _ tail =>
    intro hn hb i v ha hv
    subst n
    have hlt : i < blocks := by
      by_contra! hi
      simp [ha, feedbackLabel, Nat.not_lt_of_ge hi] at inside
    rw [hb, hv, feedbackPayload, ite_eq_left hlt] at head
    have he := (dispatcherBody_at hg hlt).mp head
    obtain ⟨next, payload, original, hl, hv⟩ := (routedFlat_body_eval _ _).mp he
    obtain ⟨e, w, rest, he, hw⟩ := tail rfl hb hl hv
    exact ⟨e, w, .step hlt original rest, he, hw⟩
  | _ => trivial

theorem packedExecution_eval (hg : FiniteCFG.HasType .nil R E g)
    {env : Env α} {s t : σ} {label : Nat} {out : Value α} :
    Eval instr env (packedExecutionRegion hg) s label out t ↔
      ∃ e v, Eval instr env g.erase s e v t ∧ label = 0 ∧ out = packedExitValue e v := by
  constructor
  · intro run
    cases run with
    | cfg entry run =>
      obtain ⟨i, v, entry, hi, hv⟩ := (routedFlat_body_eval _ _).mp entry
      obtain ⟨e, w, follow, hl, hw⟩ := follow_unpack hg run rfl (fun _ => rfl) hi hv
      exact ⟨e, w, .cfg entry follow, hl, hw⟩
  · rintro ⟨e, v, run, rfl, rfl⟩
    cases run with
    | cfg entry follow =>
      exact .cfg ((routedFlat_body_eval _ _).mpr ⟨_, _, entry, rfl, rfl⟩) (follow_pack hg follow rfl (fun _ => rfl))

private theorem packedExitValue_inj {i j : Nat} {a b : Value α} :
    packedExitValue i a = packedExitValue j b → i = j ∧ a = b := by
  induction i generalizing j with
  | zero => cases j <;> simp [packedExitValue]
  | succ i ih =>
    cases j with
    | zero => simp [packedExitValue]
    | succ j =>
      intro h
      obtain ⟨rfl, rfl⟩ := ih (Value.inr.inj h)
      exact ⟨rfl, rfl⟩

theorem packedExecution_eval_at (hg : FiniteCFG.HasType .nil R E g)
    {env : Env α} {s t : σ} {e : Nat} {v : Value α} :
    Eval instr env (packedExecutionRegion hg) s 0 (packedExitValue e v) t ↔
      Eval instr env g.erase s e v t := by
  rw [packedExecution_eval hg]
  constructor
  · rintro ⟨e', v', run, _, tagged⟩
    obtain ⟨rfl, rfl⟩ := packedExitValue_inj tagged
    exact run
  · intro run
    exact ⟨e, v, run, rfl, rfl⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution
