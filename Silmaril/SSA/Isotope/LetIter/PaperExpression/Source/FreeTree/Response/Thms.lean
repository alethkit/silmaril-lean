module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

/-! # Soundness and observations of the response-bearing model -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {n : Nat} (sorts : Fin n → α)

local notation "D" => Ty.denote (Atom S sorts)

theorem unpackArgs_injective (m : Nat) (as : Fin m → α) :
    Function.Injective (unpackArgs S sorts m as) :=
  Proofs.unpackArgs_injective S sorts m as

theorem unpackArgs_packArgs (m : Nat) (as : Fin m → α) (xs : (i : Fin m) → Tree S sorts (as i)) :
    unpackArgs S sorts m as (packArgs S sorts m as xs) = xs :=
  Proofs.unpackArgs_packArgs S sorts m as xs

section Effects

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

theorem instructions_pure :
    letI := S.endpoints
    InstructionModel.RespectsPure (ε := ε) (instructions (ε := ε) S sorts) :=
  Proofs.instructions_pure S sorts

theorem native_sound [DecidableEq α]
    {k : Nat} {β : BoundCtx (Ty α) k} {a b : Tm Empty Φ k} {A : Ty α} :
    letI := S.endpoints
    ∀ (da : Derivation Φ .nil β a A) (db : Derivation Φ .nil β b A) (ρ : BoundEnv D β),
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) β a b A →
      da.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ =
        db.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ :=
  Proofs.native_sound S sorts

/-- At a common tree return type, equality of call nodes recovers the full request,
including every input component. This remains true for an empty response type. -/
theorem recover_request {Y : Type (u + 2)} {f g : Φ}
    {x : Args S sorts f} {y : Args S sorts g}
    {k : Tree S sorts (S.out f) → ITree.Tree (Event S sorts) Y}
    {l : Tree S sorts (S.out g) → ITree.Tree (Event S sorts) Y}
    (h : ITree.vis (.call f x) k = ITree.vis (.call g y) l) :
    (⟨f, x⟩ : Request S sorts) = ⟨g, y⟩ :=
  Proofs.recover_request S sorts h

/-- For the same request, equality determines the continuation at each
free-tree response. -/
theorem recover_response {Y : Type (u + 2)} {f : Φ}
    {x : Args S sorts f}
    {k l : Tree S sorts (S.out f) → ITree.Tree (Event S sorts) Y}
    (h : ITree.vis (.call f x) k = ITree.vis (.call f x) l)
    (r : Tree S sorts (S.out f)) : k r = l r :=
  Proofs.recover_response S sorts h r

/-- After a visible instruction, equality of the bound computation is exactly
equality of its continuations at every response in the result algebra. -/
theorem eval_bind_eq_iff {Y : Type (u + 2)} {f : Φ}
    (hf : ¬ IsPure (⊥ : ε) f) (x : D (input (S.arity f) (S.arg f)))
    (k l : Atom S sorts (S.out f) → ITree.Tree (Event S sorts) Y) :
    letI := S.endpoints
    ((instructions (ε := ε) S sorts).eval f x >>= k) =
      ((instructions (ε := ε) S sorts).eval f x >>= l) ↔
      ∀ r : Tree S sorts (S.out f), k ⟨r⟩ = l ⟨r⟩ :=
  Proofs.eval_bind_eq_iff S sorts hf x k l

end Effects

/-- In particular, the model validates the entire source relation at its supplied bound. -/
theorem source_sound {ε : Type r} [HasEff Φ ε] [DecidableEq α]
    [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ} {e : ε} {A : Ty α}
    {t s : Tm Empty Φ Γ.length} :
    letI := S.endpoints
    Eqv Γ A e a b → a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
    ∀ (da : Derivation Φ .nil Γ.toBoundCtx t A) (db : Derivation Φ .nil Γ.toBoundCtx s A)
      (ρ : BoundEnv D Γ.toBoundCtx),
      da.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ =
        db.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ :=
  Proofs.source_sound S sorts

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
