module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms

/-! # Weak-tree transport on finite positional scopes -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.Morphism.CaseSSA (erase)
open Silmaril.DeBruijn (lift)

variable {E : Type w → Type w} {Φ : Type v} {α : Type u} {n labels : Nat}
variable (instr : Primitive E Φ α) {env env' : Env α} {ρ : Nat → Nat}

private theorem lift_agrees (h : ∀ i : Fin n, env' (ρ i.val) = env i.val) (value : Value α) :
    ∀ i : Fin (n + 1), (extend env' value) (lift ρ i.val) = (extend env value) i.val :=
  Fin.cases rfl h

private theorem erase_term_rename (a : LetCase.LocallyNameless.Tm Empty Φ n)
    (agree : ∀ i : Fin n, env' (ρ i.val) = env i.val) :
    term instr env' ((erase a).rename ρ) = term instr env (erase a) := by
  induction a generalizing env env' ρ with
  | fv x => exact x.elim
  | bv i => exact congrArg pure (agree i)
  | unit => rfl
  | op f a ih | inl a ih | inr a ih | abort a ih =>
    simp only [erase, LambdaSSA.Tm.rename, term, ih agree]
  | pair a b ha hb =>
    simp only [erase, LambdaSSA.Tm.rename, term, ha agree, hb agree]
  | let₁ a b ha hb =>
    simp only [erase, LambdaSSA.Tm.rename, term, ha agree, hb (lift_agrees agree _)]
  | let₂ a b ha hb =>
    simp only [erase, LambdaSSA.Tm.rename, term, ha agree]
    congr 1
    funext reply
    cases reply <;> first | rfl | exact hb (lift_agrees (lift_agrees agree _) _)
  | case a l r ha hl hr =>
    simp only [erase, LambdaSSA.Tm.rename, term, ha agree]
    congr 1
    funext reply
    cases reply <;> first | rfl | exact hl (lift_agrees agree _) | exact hr (lift_agrees agree _)

theorem flat_rename_tree (r : Flat Φ labels n)
    (agree : ∀ i : Fin n, env' (ρ i.val) = env i.val) :
    region instr env' (r.erase.renameVars ρ) = region instr env r.erase := by
  induction r generalizing env env' ρ with
  | br label arg =>
    simp only [Flat.erase, Region.renameVars, region, erase_term_rename instr arg agree]
  | let₁ a b ih =>
    simp only [Flat.erase, Region.renameVars, region, erase_term_rename instr a agree, ih (lift_agrees agree _)]
  | let₂ a b ih =>
    simp only [Flat.erase, Region.renameVars, region, erase_term_rename instr a agree]
    congr 1
    funext reply
    cases reply <;> first | rfl | exact ih (lift_agrees (lift_agrees agree _) _)
  | case a l r hl hr =>
    simp only [Flat.erase, Region.renameVars, region, erase_term_rename instr a agree]
    congr 1
    funext reply
    cases reply <;> first | rfl | exact hl (lift_agrees agree _) | exact hr (lift_agrees agree _)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction
