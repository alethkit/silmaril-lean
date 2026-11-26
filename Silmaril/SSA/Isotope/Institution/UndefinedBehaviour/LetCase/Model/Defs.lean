module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Refinement.Thms
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.ULift

/-! # Interpretation of the LetCase UB elaboration in ordered algebras -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Institution.Refinement.UB.LetCase

open Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Isotope.Theory (TypingIndex)

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]
attribute [local instance] dialectTyping
variable (P : InstrSig τ ε) (e : ε) (Γ : Ctx ν τ)

/-- Interpret the explicit language in a native ordered model, taking the fresh
constant to the value of its literal-unit spelling. -/
def explicitModel (M : OrderedAlgebra (dialectSignature P e Γ).sig) :
    OrderedAlgebra (adjoin (casePSig P.Instr Γ)).sig where
  toAlgebra :=
    let old := Algebra.reductObj (PSig.toSig (relabel P e Γ)) M.toAlgebra
    { Carrier := M.Carrier
      op := fun {i} o => match o with
        | none => fun _ => (dialectSignature P e Γ).eval M.toAlgebra (nativeUB P e Γ i)
        | some o => old.op o }
  order := M.order
  monotone_op := fun {_} o => match o with
    | none => fun _ _ _ => (M.order _).le_refl _
    | some o => (OrderedAlgebra.reductObj (PSig.toSig (relabel P e Γ)) M).monotone_op o

/-- The flag contributed by the operation symbol itself. -/
def isFresh : {i : TypingIndex τ} → (dialectSignature P e Γ).sig.Op i → Bool
  | _, .op (.inr _) => true
  | _, _ => false

/-- A concrete two-point ordered algebra for possible occurrence of UB in syntax.
All constructors combine the flags of their arguments, including both branches of a case.
A fresh primitive contributes `true`, the greatest element. -/
def flagModel : OrderedAlgebra (dialectSignature P e Γ).sig where
  toAlgebra := {
    Carrier := fun _ => ULift.{u} Bool
    op := fun o a => ULift.up (max (isFresh P e Γ o) (Finset.univ.sup (fun j => (a j).down))) }
  order _ := inferInstance
  monotone_op o a b h := by
    change max (isFresh P e Γ o) (Finset.univ.sup (fun j => (a j).down)) ≤
      max (isFresh P e Γ o) (Finset.univ.sup (fun j => (b j).down))
    exact max_le_max le_rfl (Finset.sup_mono_fun (fun j _ => h j))

end Silmaril.Isotope.Institution.Refinement.UB.LetCase
