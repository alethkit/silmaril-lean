module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.VisibleDepth.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Categorical.Thms
public import Silmaril.Semantics.ITree.VisiblePrefix.Thms

/-! # Visible-depth soundness for mixed request trees -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.VisibleDepthProofs

universe u r v w

section Mixed

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

public theorem denote_visibleDepth {n m : Nat} {slots : Fin n → α} (modelSlots : Fin m → α)
    (p : Program S T c slots) (vars : (i : Fin n) → Tree S modelSlots (slots i)) :
    ITree.VisibleDepthLE (p.denote S T modelSlots vars) p.visibleDepth := by
  induction p with
  | ret => exact ITree.visibleDepthLE_ret _
  | atom f args next ih => exact ITree.visibleDepthLE_vis _ _ _ (fun r => ih (extendValues S modelSlots r vars))
  | sum g args left right ihl ihr =>
    apply ITree.visibleDepthLE_vis
    intro reply
    cases reply with
    | inl r => exact (ihl (extendValues S modelSlots r vars)).mono (le_max_left _ _)
    | inr r => exact (ihr (extendValues S modelSlots r vars)).mono (le_max_right _ _)

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  [DecidableEq α] {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

public theorem raw_denote_visibleDepth (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Raw.Program S T c slots) (hp : p.WellTyped S T e)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : p.source.toLetIter Γ.length = some t)
    {m : Nat} (modelSlots : Fin m → α) (vars : (i : Fin Γ.length) → Tree S modelSlots (slots i))
    (d : letI := endpoints S T; Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx t (.base c)) :
    letI := endpoints S T
    ITree.VisibleDepthLE (d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots)
      (fun x => x.elim) (variableEnv S modelSlots hs vars)) (p.visibleDepth (ε := ε)) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  obtain ⟨dq, hq⟩ := eval_exists S T modelSlots hs e _ (Raw.compile_typed S T e p hp)
  have hn := (Raw.compile_native S T hΓ hs e p hp ht).2.2
  rw [LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil.{u, u + 2, u, r}
    (Atom S modelSlots) _ (instructions_respectsPure S T modelSlots visible) hn d dq
      (variableEnv S modelSlots hs vars), hq vars]
  exact denote_visibleDepth S T modelSlots _ vars

end Mixed

section LoopFree

variable {α : Type u} {F : α → Type (max u (v + 1))}
  {Φ : Type w} [HasTy Φ (Ty α)] {E : Type v → Type v}

local notation "D" => Ty.denote F

private theorem pure_depth {X : Type (max u (v + 1))} (x : X) :
    ITree.VisibleDepthLE (pure x : ITree.Tree E X) 0 :=
  ITree.visibleDepthLE_ret x

private theorem loopFree_bounded {n : Nat} {β : BoundCtx (Ty α) n} {t : Tm Empty Φ n} {A : Ty α}
    (M : InstructionModel D Φ (ITree.Tree E))
    (hInstr : ∀ f x, ITree.VisibleDepthLE (M.eval f x) 1)
    (d : Derivation Φ (.nil : Ctx Empty (Ty α)) β t A) (h : LoopFree t) :
    ∃ bound, ∀ ρ, ITree.VisibleDepthLE (d.denote D M (fun x => x.elim) ρ) bound := by
  induction d with
  | fv h => exact ⟨0, fun _ => pure_depth _⟩
  | bv => exact ⟨0, fun _ => pure_depth _⟩
  | unit => exact ⟨0, fun _ => pure_depth _⟩
  | op d ih =>
    obtain ⟨b, hb⟩ := ih h
    exact ⟨b + 1, fun ρ => ITree.visibleDepthLE_bind _ _ (hb ρ) (hInstr _)⟩
  | let₁ da db iha ihb =>
    obtain ⟨a, ha⟩ := iha h.1
    obtain ⟨b, hb⟩ := ihb h.2
    exact ⟨a + b, fun ρ => ITree.visibleDepthLE_bind _ _ (ha ρ) (fun v => hb (ρ.snoc v))⟩
  | pair da db iha ihb =>
    obtain ⟨a, ha⟩ := iha h.1
    obtain ⟨b, hb⟩ := ihb h.2
    refine ⟨a + b, fun ρ => ITree.visibleDepthLE_bind _ _ (ha ρ) ?_⟩
    intro v
    exact ITree.visibleDepthLE_bind _ _ (hb ρ) (fun w => pure_depth _)
  | let₂ da db iha ihb =>
    obtain ⟨a, ha⟩ := iha h.1
    obtain ⟨b, hb⟩ := ihb h.2
    exact ⟨a + b, fun ρ => ITree.visibleDepthLE_bind _ _ (ha ρ) (fun p => hb ((ρ.snoc p.1).snoc p.2))⟩
  | inl d ih =>
    obtain ⟨b, hb⟩ := ih h
    exact ⟨b, fun ρ => ITree.visibleDepthLE_bind _ _ (hb ρ) (fun v => pure_depth _)⟩
  | inr d ih =>
    obtain ⟨b, hb⟩ := ih h
    exact ⟨b, fun ρ => ITree.visibleDepthLE_bind _ _ (hb ρ) (fun v => pure_depth _)⟩
  | case dq dl dr ihq ihl ihr =>
    obtain ⟨q, hq⟩ := ihq h.1
    obtain ⟨l, hl⟩ := ihl h.2.1
    obtain ⟨r, hr⟩ := ihr h.2.2
    refine ⟨q + max l r, fun ρ => ITree.visibleDepthLE_bind _ _ (hq ρ) ?_⟩
    intro res
    cases res with
    | inl v => exact (hl (ρ.snoc v)).mono (le_max_left _ _)
    | inr v => exact (hr (ρ.snoc v)).mono (le_max_right _ _)
  | abort d ih =>
    obtain ⟨b, hb⟩ := ih h
    exact ⟨b, fun ρ => ITree.visibleDepthLE_bind _ _ (b := 0) (hb ρ) (fun v => v.elim)⟩
  | iter => exact False.elim h

end LoopFree

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {ε : Type w} [HasEff Φ ε] [Bot ε]

private theorem instruction_bound {m : Nat} (modelSlots : Fin m → α) :
    letI := endpoints S T
    ∀ f x, ITree.VisibleDepthLE ((SumCall.instructions (ε := ε) S T modelSlots).eval f x) 1 := by
  let instr := endpoints S T
  intro f x
  cases f with
  | inl f =>
    by_cases h : IsPure (⊥ : ε) f
    · simp only [SumCall.instructions, ite_eq_left h]
      exact (ITree.visibleDepthLE_ret _).mono (Nat.zero_le _)
    · simp only [SumCall.instructions, ite_eq_right h]
      exact ITree.visibleDepthLE_vis _ _ 0 (fun _ => ITree.visibleDepthLE_ret _)
  | inr g => exact ITree.visibleDepthLE_vis _ _ 0 (fun _ => ITree.visibleDepthLE_ret _)

public theorem written_denote_bounded {n m : Nat} {β : BoundCtx (Ty α) n} {A : Ty α}
    (modelSlots : Fin m → α) (p : Expr (Φ ⊕ Ψ)) {t : Tm Empty (Φ ⊕ Ψ) n} (ht : p.toLetIter n = some t)
    (d : letI := endpoints S T; Derivation (Φ ⊕ Ψ) (.nil : Ctx Empty (Ty α)) β t A) :
    letI := endpoints S T
    ∃ bound, ∀ ρ, ITree.VisibleDepthLE
      (d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots) (fun x => x.elim) ρ)
      bound := by
  let instr := endpoints S T
  exact loopFree_bounded (SumCall.instructions (ε := ε) S T modelSlots) (instruction_bound S T modelSlots)
    d (loopFree_of_lowering ht)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.VisibleDepthProofs
