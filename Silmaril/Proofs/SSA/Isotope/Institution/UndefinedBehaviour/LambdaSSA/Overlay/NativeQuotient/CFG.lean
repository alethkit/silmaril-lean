module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.LambdaSSA.UB.Overlay

universe u v w x

variable {Φ : Type u}

private theorem cfgZero_obs (entry : LambdaSSA.Region Φ) (blocks : Fin 0 → LambdaSSA.Region Φ) :
    LambdaSSA.Region.Obs.{u,w,x} (.cfg entry 0 blocks) entry where
  eval := by
    intro α σ instr env s s' label out
    constructor
    · intro h
      cases h with
      | cfg head tail =>
        cases tail with
        | exit _ => simpa only [Nat.sub_zero] using head
        | step inside _ _ => exact (Nat.not_lt_zero _ inside).elim
    · intro h
      simpa only [Nat.sub_zero] using Semantics.Region.Eval.cfg h
        (Semantics.Region.Follow.exit (blocks := blocks) (Nat.zero_le label))
  fault := by
    intro α σ instr faults env s s'
    constructor
    · intro h
      cases h with
      | cfg_entry fault => exact fault
      | cfg_follow _ tail => cases tail with
        | body inside _ | step inside _ _ => exact (Nat.not_lt_zero _ inside).elim
    · exact Semantics.Region.Fault.cfg_entry
  diverges := by
    intro α σ instr prim env s
    constructor
    · intro h
      cases h.unfold with
      | core step =>
        cases step with
        | cfg_entry body => exact body
        | cfg_follow _ rest =>
          cases rest.unfold with
          | core next => cases next with
            | follow_body inside _ | follow_next inside _ _ => exact (Nat.not_lt_zero _ inside).elim
    · exact fun h => External.Diverges.fold_core (.cfg_entry h)

private theorem cfgBrExit_obs {n : Nat} (label : Nat) (a : LambdaSSA.Tm Φ)
    (blocks : Fin n → LambdaSSA.Region Φ) :
    LambdaSSA.Region.Obs.{u,w,x} (.cfg (.br (n + label) a) n blocks) (.br label a) where
  eval := by
    intro α σ instr env s s' out value
    constructor
    · intro h
      cases h with
      | cfg head tail =>
        cases head with
        | br arg =>
          cases tail with
          | exit _ => simpa only [Nat.add_sub_cancel_left] using Semantics.Region.Eval.br arg
          | step inside _ _ => omega
    · intro h
      cases h with
      | br arg =>
        refine Semantics.Region.Eval.cfg (Semantics.Region.Eval.br arg) ?_
        simpa only [Nat.add_sub_cancel_left] using
          (Semantics.Region.Follow.exit (blocks := blocks) (Nat.le_add_right n label))
  fault := by
    intro α σ instr faults env s s'
    constructor
    · intro h
      cases h with
      | cfg_entry failure => cases failure with
        | br arg => exact .br arg
      | cfg_follow head tail =>
        cases head
        cases tail with
        | body inside _ | step inside _ _ => omega
    · intro h
      cases h with
      | br arg => exact .cfg_entry (.br arg)
  diverges := by
    intro α σ instr prim env s
    constructor
    · intro h
      cases h.unfold with
      | core step =>
        cases step with
        | cfg_entry body =>
          cases body.unfold with
          | core step => cases step
          | br arg => exact External.Diverges.fold (.br arg)
        | cfg_follow head rest =>
          cases head
          cases rest.unfold with
          | core next =>
            cases next with
            | follow_body inside _ | follow_next inside _ _ => omega
    · intro h
      cases h.unfold with
      | core step => cases step
      | br arg => exact External.Diverges.fold_core (.cfg_entry (External.Diverges.fold (.br arg)))

/-- Both entries evaluate the same argument once. The local entry branch
takes the selected block's first step before reaching the same follow state. -/
private theorem cfgBrLocal_obs {n : Nat} (i : Fin n) (a : LambdaSSA.Tm Φ)
    (blocks : Fin n → LambdaSSA.Region Φ) :
    LambdaSSA.Region.Obs.{u,w,x} (.cfg (.br i a) n blocks) (.cfg (.let₁ a (blocks i)) n blocks) where
  eval := by
    intro α σ instr env s s' label value
    constructor
    · intro h
      cases h with
      | cfg head tail =>
        cases head with
        | br arg =>
          cases tail with
          | exit outside => exact (Nat.not_le_of_lt i.isLt outside).elim
          | step _ body rest => exact .cfg (.let₁ arg body) rest
    · intro h
      cases h with
      | cfg head tail =>
        cases head with
        | let₁ arg body => exact .cfg (.br arg) (.step i.isLt body tail)
  fault := by
    intro α σ instr faults env s s'
    constructor
    · intro h
      cases h with
      | cfg_entry failure => cases failure with
        | br arg => exact .cfg_entry (.let₁_arg arg)
      | cfg_follow head tail =>
        cases head with
        | br arg =>
          cases tail with
          | body _ fault => exact .cfg_entry (.let₁_body arg fault)
          | step _ body rest => exact .cfg_follow (.let₁ arg body) rest
    · intro h
      cases h with
      | cfg_entry failure =>
        cases failure with
        | let₁_arg arg => exact .cfg_entry (.br arg)
        | let₁_body arg body => exact .cfg_follow (.br arg) (.body i.isLt body)
      | cfg_follow head tail =>
        cases head with
        | let₁ arg body => exact .cfg_follow (.br arg) (.step i.isLt body tail)
  diverges := by
    intro α σ instr prim env s
    constructor
    · intro h
      cases h.unfold with
      | core step =>
        cases step with
        | cfg_entry body =>
          cases body.unfold with
          | core next => cases next
          | br arg => exact External.Diverges.fold_core (.cfg_entry
              (External.Diverges.fold (.let₁_arg arg)))
        | cfg_follow head tail =>
          cases head with
          | br arg =>
            cases tail.unfold with
            | core next =>
              cases next with
              | follow_body _ body => exact External.Diverges.fold_core (.cfg_entry
                  (External.Diverges.fold_core (.let₁ arg body)))
              | follow_next _ body rest =>
                exact External.Diverges.fold_core (.cfg_follow (.let₁ arg body) rest)
    · intro h
      cases h.unfold with
      | core step =>
        cases step with
        | cfg_entry entry =>
          cases entry.unfold with
          | let₁_arg arg => exact External.Diverges.fold_core (.cfg_entry
              (External.Diverges.fold (.br arg)))
          | core next =>
            cases next with
            | let₁ arg body => exact External.Diverges.fold_core (.cfg_follow (.br arg)
                (External.Diverges.fold_core (.follow_body i.isLt body)))
        | cfg_follow head tail =>
          cases head with
          | let₁ arg body => exact External.Diverges.fold_core (.cfg_follow (.br arg)
              (External.Diverges.fold_core (.follow_next i.isLt body tail)))

variable {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L : List τ}

theorem cfgEquiv_obs {r s : LambdaSSA.Region Φ} (h : LambdaSSA.Region.CfgEquiv Γ r s L) :
    LambdaSSA.Region.Obs.{u,w,x} r s := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ left right => exact left.trans right
  | let₁ _ _ ih => exact .let₁ (.refl _) ih
  | let₂ _ _ ih => exact .let₂ (.refl _) ih
  | case _ _ _ left right => exact .case (.refl _) left right
  | cfg _ _ _ entry blocks => exact .cfg entry blocks
  | cfgZero _ blocks => exact cfgZero_obs _ blocks
  | cfgBrExit _ _ _ _ => exact cfgBrExit_obs _ _ _
  | cfgBrLocal _ i _ _ => exact cfgBrLocal_obs i _ _

theorem nativeDenotation_eq {r s : LambdaSSA.Region.TypedRegion (Φ := Φ) Γ L}
    (h : LambdaSSA.Region.Obs.{u,w,x} r.val s.val) :
    nativeDenotation.{u,v,w,x} r = nativeDenotation.{u,v,w,x} s := by
  funext M state
  have observations : UB.observe M ⟨r.val, r.property⟩ = UB.observe M ⟨s.val, s.property⟩ :=
    ssaBeh_eq_of_obs h M
  change WithTop.some (nativeOutcomes ⟨r.val, r.property⟩ M state) =
    WithTop.some (nativeOutcomes ⟨s.val, s.property⟩ M state)
  apply congrArg WithTop.some
  exact Set.ext fun _ => by simp only [nativeOutcomes, Set.mem_ofPred_eq, observations]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay
