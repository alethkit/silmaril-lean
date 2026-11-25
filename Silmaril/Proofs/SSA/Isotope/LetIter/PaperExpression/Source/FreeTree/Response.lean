module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Defs

/-! # Soundness and observations of the response-bearing model -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.Semantics.Categorical (denote_eq_of_abortEquiv_nil)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Proofs

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {n : Nat} (sorts : Fin n → α)

local notation "D" => Ty.denote (Atom S sorts)

public theorem unpackArgs_injective (m : Nat) (as : Fin m → α) :
    Function.Injective (unpackArgs S sorts m as) := by
  induction m with
  | zero => intro p q _; exact Subsingleton.elim (α := PUnit.{u + 3}) p q
  | succ m ih =>
    intro p q h
    apply Prod.ext
    · exact ULift.ext (congrFun h 0)
    · apply ih (fun i => as i.succ)
      funext i
      exact congrFun h i.succ

public theorem unpackArgs_packArgs (m : Nat) (as : Fin m → α) (xs : (i : Fin m) → Tree S sorts (as i)) :
    unpackArgs S sorts m as (packArgs S sorts m as xs) = xs := by
  induction m with
  | zero => funext i; exact i.elim0
  | succ m ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih _ _) j

section Effects

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

public theorem instructions_pure :
    letI := S.endpoints
    InstructionModel.RespectsPure (ε := ε) (instructions (ε := ε) S sorts) := by
  let instr := S.endpoints
  intro f hf
  exact ⟨fun x => ⟨.op f (readArgs S sorts f x)⟩, fun x => by
    simp [instructions, IsPure, hf]
    rfl⟩

public theorem native_sound [DecidableEq α]
    {k : Nat} {β : BoundCtx (Ty α) k} {a b : Tm Empty Φ k} {A : Ty α} :
    letI := S.endpoints
    ∀ (da : Derivation Φ .nil β a A) (db : Derivation Φ .nil β b A) (ρ : BoundEnv D β),
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) β a b A →
      da.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ =
        db.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ := by
  let instr := S.endpoints
  intro da db ρ h
  exact denote_eq_of_abortEquiv_nil.{u, u + 2, u, r} (Atom S sorts) _
    (instructions_pure S sorts) h da db ρ

/-- At a common tree return type, equality of call nodes recovers the full request,
including every input component. This remains true for an empty response type. -/
public theorem recover_request {Y : Type (u + 2)} {f g : Φ}
    {x : Args S sorts f} {y : Args S sorts g}
    {k : Tree S sorts (S.out f) → ITree.Tree (Event S sorts) Y}
    {l : Tree S sorts (S.out g) → ITree.Tree (Event S sorts) Y}
    (h : ITree.vis (.call f x) k = ITree.vis (.call g y) l) :
    (⟨f, x⟩ : Request S sorts) = ⟨g, y⟩ := by
  have he := congrArg (fun t => (ITree.out t).map (visibleRequest S sorts)) h
  simpa only [ITree.out_vis, Part.map_eq_map, Part.map_some, Part.some_inj,
    visibleRequest, Option.some.injEq] using he

/-- For the same request, equality determines the continuation at each
free-tree response. -/
public theorem recover_response {Y : Type (u + 2)} {f : Φ}
    {x : Args S sorts f}
    {k l : Tree S sorts (S.out f) → ITree.Tree (Event S sorts) Y}
    (h : ITree.vis (.call f x) k = ITree.vis (.call f x) l)
    (r : Tree S sorts (S.out f)) : k r = l r := by
  exact congrFun ((ITree.vis_inj (Event.call f x) k l).mp h) r

/-- After a visible instruction, equality of the bound computation is exactly
equality of its continuations at every response in the result algebra. -/
public theorem eval_bind_eq_iff {Y : Type (u + 2)} {f : Φ}
    (hf : ¬ IsPure (⊥ : ε) f) (x : D (input (S.arity f) (S.arg f)))
    (k l : Atom S sorts (S.out f) → ITree.Tree (Event S sorts) Y) :
    letI := S.endpoints
    ((instructions (ε := ε) S sorts).eval f x >>= k) =
      ((instructions (ε := ε) S sorts).eval f x >>= l) ↔
      ∀ r : Tree S sorts (S.out f), k ⟨r⟩ = l ⟨r⟩ := by
  classical
  let instr := S.endpoints
  change ((if IsPure (⊥ : ε) f then ITree.ret ⟨.op f (readArgs S sorts f x)⟩
      else ITree.vis (.call f (readArgs S sorts f x)) (fun r => pure (⟨r⟩ : Atom S sorts (S.out f)))) >>= k) =
      ((if IsPure (⊥ : ε) f then ITree.ret ⟨.op f (readArgs S sorts f x)⟩
      else ITree.vis (.call f (readArgs S sorts f x)) (fun r => pure (⟨r⟩ : Atom S sorts (S.out f)))) >>= l) ↔ _
  rw [ite_eq_right hf, ITree.vis_bind, ITree.vis_bind, ITree.vis_inj]
  simp only [pure_bind]
  exact ⟨congrFun, funext⟩

end Effects

/-- In particular, the model validates the entire source relation at its supplied bound. -/
public theorem source_sound {ε : Type r} [HasEff Φ ε] [DecidableEq α]
    [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ} {e : ε} {A : Ty α}
    {t s : Tm Empty Φ Γ.length} :
    letI := S.endpoints
    Eqv Γ A e a b → a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
    ∀ (da : Derivation Φ .nil Γ.toBoundCtx t A) (db : Derivation Φ .nil Γ.toBoundCtx s A)
      (ρ : BoundEnv D Γ.toBoundCtx),
      da.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ =
        db.denote D (instructions (ε := ε) S sorts) (fun x => x.elim) ρ := by
  let instr := S.endpoints
  intro h ht hs da db ρ
  exact Response.Proofs.native_sound S sorts da db ρ (h.toLetIter ht hs)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Proofs
