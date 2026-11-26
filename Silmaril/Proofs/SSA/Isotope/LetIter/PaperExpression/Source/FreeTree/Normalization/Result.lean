module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Result.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree

/-! # The weak-tree interpretation separates pure normal values -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation)
open Silmaril.Isotope.LetIter.Semantics.Categorical (denote_eq_of_abortEquiv_nil)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Value.Proofs

universe u v r
variable {α Φ : Type u} (S : Signature α Φ) {n : Nat} {sorts : Fin n → α}

public theorem denoteWith_injective {F : α → Type v} (atom : ∀ {a}, Tree S sorts a → F a)
    (hinj : ∀ a, Function.Injective (@atom a)) {A : Ty α} :
    Function.Injective (denoteWith S atom (A := A)) := by
  intro p
  induction p with
  | tree p =>
    intro q he
    cases q with | tree q => exact congrArg Value.tree (hinj _ he)
  | unit => intro q _; cases q; rfl
  | pair p q ihp ihq =>
    intro r he
    cases r with
    | pair p' q' => exact congrArg₂ Value.pair (ihp (congrArg Prod.fst he)) (ihq (congrArg Prod.snd he))
  | inl p ih =>
    intro q he
    cases q with
    | inl q => exact congrArg Value.inl (ih (Sum.inl.inj he))
    | inr q => cases he
  | inr p ih =>
    intro q he
    cases q with
    | inl q => cases he
    | inr q => exact congrArg Value.inr (ih (Sum.inr.inj he))

public theorem denote_injective {A : Ty α} :
    Function.Injective (denote S (sorts := sorts) (A := A)) :=
  denoteWith_injective S (fun t => t) (fun _ => Function.injective_id)

public theorem lowers {A : Ty α} (p : Value S sorts A) :
    (p.source S).toLetIter n = some (native S p) := by
  induction p with
  | tree t => exact tree_lowers S t
  | _ => simp [Value.source, Expr.toLetIter, native, *]

section Typed

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "β" => Γ.toBoundCtx
local notation "D" => Ty.denote (Tree S slots)

noncomputable def derivation {A : Ty α} (p : Value S slots A)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) :
    letI := S.endpoints
    Derivation Φ Γ₀ β (native S p) A := by
  let instr := S.endpoints
  induction p with
  | tree t => exact FreeTree.Proofs.treeDerivation S t hslots
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

theorem eval_returns {A : Ty α} (p : Value S slots A)
    (hp : p.Pure (ε := ε) S)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (observe : ObserveInput (sorts := slots) S) :
    letI := S.endpoints
    (derivation S p hslots).denote D (instructions (ε := ε) S observe)
        (FreeTree.Proofs.eliminateFree S) (FreeTree.Proofs.values S hslots) =
      ITree.ret (denote S p) := by
  let instr := S.endpoints
  induction p with
  | tree t => exact FreeTree.Proofs.tree_eval_returns S t observe hp hslots
  | unit => rfl
  | @pair A B p q ihp ihq =>
    change ((derivation S p hslots).denote D (instructions (ε := ε) S observe)
        (FreeTree.Proofs.eliminateFree S) (FreeTree.Proofs.values S hslots) >>= fun x =>
      (derivation S q hslots).denote D (instructions (ε := ε) S observe)
        (FreeTree.Proofs.eliminateFree S) (FreeTree.Proofs.values S hslots) >>= fun y =>
      ITree.ret ((x, y) : D (.product A B))) = _
    rw [ihp hp.1, ihq hp.2]
    erw [pure_bind]
    erw [pure_bind]
    rfl
  | @inl A B p ih =>
    change ((derivation S p hslots).denote D (instructions (ε := ε) S observe)
        (FreeTree.Proofs.eliminateFree S) (FreeTree.Proofs.values S hslots) >>= fun x =>
      ITree.ret (Sum.inl x : D (.coprod A B))) = _
    rw [ih hp]
    erw [pure_bind]
    rfl
  | @inr A B q ih =>
    change ((derivation S q hslots).denote D (instructions (ε := ε) S observe)
        (FreeTree.Proofs.eliminateFree S) (FreeTree.Proofs.values S hslots) >>= fun y =>
      ITree.ret (Sum.inr y : D (.coprod A B))) = _
    rw [ih hp]
    erw [pure_bind]
    rfl

variable [DecidableEq α]

public theorem native_eq_implies_value_eq {A : Ty α} (p q : Value S slots A)
    (hp : p.Pure (ε := ε) S) (hq : q.Pure (ε := ε) S)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (h : letI := S.endpoints
      AbortEquiv (⊥ : ε) Γ₀ β (native S p) (native S q) A) : p = q := by
  let instr := S.endpoints
  let observe : ObserveInput (sorts := slots) S := fun _ _ => false
  have he := denote_eq_of_abortEquiv_nil.{u, u+1, u, r} (Tree S slots)
    (instructions (ε := ε) S observe) (instructions_pure S observe)
    h (derivation S p hslots) (derivation S q hslots) (FreeTree.Proofs.values S hslots)
  have hr := (eval_returns S p hp hslots observe).symm.trans
    (he.trans (eval_returns S q hq hslots observe))
  exact denote_injective S (ITree.ret_inj.mp hr)

end Typed

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Value.Proofs
