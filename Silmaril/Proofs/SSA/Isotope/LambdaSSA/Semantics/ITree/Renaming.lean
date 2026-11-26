module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! # Weak interaction trees and value renamings -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend extend_rename)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction

variable {F : Type w → Type w} {Φ : Type v} {α : Type u} (instr : Primitive F Φ α)
  {env env' : Env α} {ρ : Nat → Nat}

theorem term_rename (a : Tm Φ) (h : ∀ i, env' (ρ i) = env i) :
    term instr env' (a.rename ρ) = term instr env a := by
  induction a generalizing env env' ρ with
  | var i => simp [term, Tm.rename, h]
  | unit => rfl
  | op op a ih | inl a ih | inr a ih | abort a ih =>
    simp only [Tm.rename, term, ih h]
  | pair a b iha ihb => simp only [Tm.rename, term, iha h, ihb h]
  | let₁ a b iha ihb => simp only [Tm.rename, term, iha h, ihb (extend_rename h _)]
  | let₂ a b iha ihb =>
    simp only [Tm.rename, term, iha h]
    congr 1
    funext val
    cases val <;> first | rfl | exact ihb (extend_rename (extend_rename h _) _)
  | case a l r iha ihl ihr =>
    simp only [Tm.rename, term, iha h]
    congr 1
    funext val
    cases val <;> first | rfl | exact ihl (extend_rename h _) | exact ihr (extend_rename h _)

theorem region_renameVars (r : Region Φ) (h : ∀ i, env' (ρ i) = env i) :
    region instr env' (r.renameVars ρ) = region instr env r := by
  induction r generalizing env env' ρ with
  | br i a => simp only [Region.renameVars, region, term_rename instr a h]
  | let₁ a b ih => simp only [Region.renameVars, region, term_rename instr a h, ih (extend_rename h _)]
  | let₂ a b ih =>
    simp only [Region.renameVars, region, term_rename instr a h]
    congr 1
    funext val
    cases val <;> first | rfl | exact ih (extend_rename (extend_rename h _) _)
  | case a l r ihl ihr =>
    simp only [Region.renameVars, region, term_rename instr a h]
    congr 1
    funext val
    cases val <;> first | rfl | exact ihl (extend_rename h _) | exact ihr (extend_rename h _)
  | cfg e arity blocks ihe ihb =>
    simp only [Region.renameVars, region, ihe h, ihb _ (extend_rename h _)]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction
