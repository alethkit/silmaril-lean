module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Translation

/-! # Typed translation and denotation of structured acyclic λSSA -/

public section

universe u v w q

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Code

open LetCase.LocallyNameless (Derivation)
open Isotope.Semantics (BoundEnv FreeEnv InstructionModel ProductModel UnitModel CoproductModel EmptyModel)
open LambdaSSA.Semantics (Env)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- The raw λSSA embedding types in every exit context supplying the selected label. -/
theorem toSSA_hasType (c : Code Φ β A) {L : LCtx τ} {exit : Nat}
    (h : At L exit A) : Region.HasType β.toList (c.toSSA exit) L :=
  Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.toSSA_hasType c h

/-- Translating reified LetCase back recovers both the term and its exact typing derivation. -/
@[simp] theorem toLetCase_ofLetCase {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) :
    (ofLetCase d).toLetCase = ⟨t, d⟩ :=
  Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.toLetCase_ofLetCase d

/-- Both directions of finite evaluation agree on the selected exit, payload
and final state, for any shared primitive transition relation. -/
theorem eval_toSSA_iff (c : Code Φ β A)
    {α : Type w} {σ : Type q} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Env α} {bound : LetCase.Semantics.BoundEnv α n}
    {s s' : σ} {value : Value α} {exit label : Nat} (agree : Morphism.CaseSSA.EnvAgrees env bound) :
    LambdaSSA.Semantics.Region.Eval instr env (c.toSSA exit) s label value s' ↔
      label = exit ∧ LetCase.Semantics.Eval instr Empty.elim bound c.toLetCase.1 s value s' :=
  Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.eval_toSSA_iff c agree

/-- Reifying the compiled term preserves and reflects every finite SSA outcome. -/
theorem eval_roundtrip_iff (c : Code Φ β A)
    {α : Type w} {σ : Type q} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Env α} {s s' : σ} {value : Value α} {exit label : Nat} :
    LambdaSSA.Semantics.Region.Eval instr env (c.toSSA exit) s label value s' ↔
      LambdaSSA.Semantics.Region.Eval instr env
        ((ofLetCase c.toLetCase.2).toSSA exit) s label value s' := by
  rw [eval_toSSA_iff c (bound := fun i => env i.val) (fun _ => rfl),
    eval_toSSA_iff _ (bound := fun i => env i.val) (fun _ => rfl), toLetCase_ofLetCase]

section Denotation

variable {κ : Type u} {F : κ → Type u} {σ : Type u}
  {Φ : Type v} [HasTy Φ (Ty κ)] {n : Nat} {β : BoundCtx (Ty κ) n} {A : Ty κ}
  {M : InstructionModel (Ty.denote F) Φ (StateT σ SetM)}
  {instr : Φ → Value (Sigma F) → σ → Value (Sigma F) → σ → Prop}

/-- Evaluating the existing λSSA region and translating to the typed LetCase
state-and-powerset model give the same finite outcomes. The primitive operations
must agree, including their state transitions. -/
theorem eval_iff_denote (c : Code Φ β A)
    (compatible : M.Compatible F instr) (ρ : BoundEnv (Ty.denote F) β)
    {env : Env (Sigma F)} {exit label : Nat} {s s' : σ} {value : Value (Sigma F)}
    (hρ : BoundEnv.Encodes F ρ (fun i => env i.val)) :
    LambdaSSA.Semantics.Region.Eval instr env (c.toSSA exit) s label value s' ↔
      label = exit ∧ ∃ a, value = Isotope.Semantics.encodeValue F A a ∧
        (a, s') ∈ (c.toLetCase.2.denote (Ty.denote F) M (fun x => nomatch x) ρ s).run := by
  rw [eval_toSSA_iff c (bound := fun i => env i.val) (fun _ => rfl)]
  exact and_congr_right fun _ => LetCase.Semantics.eval_iff_denote F M instr compatible
    c.toLetCase.2 _ ρ _ _ (fun x => nomatch x) hρ s value s'

end Denotation

/-- The existing LetSeq inclusion commutes with reification and translation
back in any shared typed monadic model. -/
theorem denote_ofLetSeq {t : LetSeq.LocallyNameless.Tm Empty Φ n}
    (d : LetSeq.LocallyNameless.Derivation Φ (.nil : Ctx Empty τ) β t A)
    (D : τ → Type w) [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    {m : Type w → Type w} [Monad m] (M : InstructionModel D Φ m)
    (γ : FreeEnv D (.nil : Ctx Empty τ)) (ρ : BoundEnv D β) :
    (ofLetCase (Morphism.SeqCase.derivation d)).toLetCase.2.denote D M γ ρ = d.denote D M γ ρ := by
  rw [toLetCase_ofLetCase]
  exact Morphism.SeqCase.denote_derivation D M d γ ρ

end Silmaril.Isotope.LambdaSSA.Acyclic.Code
