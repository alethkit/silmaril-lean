module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Refinement.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Quantitative.Thms
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-! A UB loop body is canonical under the iteration binder. A two-point model
of the matched ground axioms separates the native fixpoint equation. -/

open CategoryTheory
open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Institution Silmaril.Isotope.Institution.Refinement
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel

namespace LetIterUBRegression

attribute [local instance] UB.dialectTyping

private abbrev τ := Ty Empty

private def alphabet : InstrSig τ Bool where
  Instr := Empty
  hasTy := ⟨Empty.elim, Empty.elim⟩
  hasEff := ⟨Empty.elim⟩

private abbrev Γ : Ctx Empty τ := .nil
private abbrev closed : TypingIndex τ := ⟨0, .nil, unit⟩
private abbrev S := (iterPSig alphabet.Instr Γ).sig
private abbrev E {n : Nat} (β : BoundCtx τ n) (A : τ) :=
  UB.LetIter.Explicit alphabet Γ ⟨n, β, A⟩

private def unitAt {n : Nat} (β : BoundCtx τ n) : E β unit :=
  UB.Expr.node (S := S) (Models.Operation.unit (β := β)) (fun j => Fin.elim0 j)

private def varAt {n : Nat} (β : BoundCtx τ n) (i : Fin n) : E β (β.get i) :=
  UB.Expr.node (S := S) (Models.Operation.bv (β := β) i) (fun j => Fin.elim0 j)

private def iterUB {n : Nat} (β : BoundCtx τ n) (a : E β unit) : E β unit :=
  let op : S.Op ⟨n, β, unit⟩ := Models.Operation.iter (β := β) unit unit
  UB.Expr.node op (Fin.cases (motive := fun j => UB.Expr S (S.argSort op j))
    (by exact a) (fun _ => UB.Expr.ub))

private def loop : E .nil unit := iterUB .nil (unitAt .nil)

private def unfoldLoop : E .nil unit :=
  let β : BoundCtx τ 1 := .snoc .nil unit
  let arms := β.snoc unit
  let caseOp : S.Op ⟨1, β, unit⟩ := Models.Operation.case (β := β) unit unit unit
  let body : E β unit := UB.Expr.node caseOp
    (Fin.cases (motive := fun j => UB.Expr S (S.argSort caseOp j)) UB.Expr.ub
      (Fin.cases (motive := fun j : Fin 2 => UB.Expr S (S.argSort caseOp j.succ))
        (by exact varAt arms 0) (fun _ => by exact iterUB arms (varAt arms 0))))
  let bindOp : S.Op closed := Models.Operation.let₁ (β := .nil) unit unit
  UB.Expr.node bindOp (Fin.cases (motive := fun j => UB.Expr S (S.argSort bindOp j))
    (by exact unitAt .nil) (fun _ => by exact body))

example : (UB.LetIter.typedEquiv alphabet true Γ closed loop).val.1 =
    .iter .unit (.op (Sum.inr (coprod unit unit)) .unit) := rfl

example : (UB.LetIter.typedEquiv alphabet true Γ closed).symm
    (UB.LetIter.typedEquiv alphabet true Γ closed loop) = loop :=
  Equiv.symm_apply_apply _ _

private abbrev R : TypedRelation Empty alphabet.Instr τ := fun _ _ _ _ => False
private abbrev axioms := (iterTheory false Γ R).sentences

example : UB.LetIter.nativeRefines alphabet true false Γ R
    (UB.LetIter.encode alphabet true Γ unfoldLoop) (UB.LetIter.encode alphabet true Γ loop) := by
  let := (UB.dialect alphabet true).hasEff
  let lhs := UB.LetIter.encode alphabet true Γ loop
  let rhs := UB.LetIter.encode alphabet true Γ unfoldLoop
  exact .equiv (.symm (.ax (.iteration (.fixpoint .unit (.op (Sum.inr (coprod unit unit)) .unit)))
    lhs.2.toHasType rhs.2.toHasType))

private abbrev baseSig := iterPSig alphabet.Instr Γ
private noncomputable abbrev explicitSig := UB.adjoin baseSig

-- Old terms always give false. The interpretation of iteration reads just
-- its seed, while case includes the flag of its scrutinee.
private def flagOp : {i : TypingIndex τ} → (o : (UB.signature S).Op i) →
    (Fin ((UB.signature S).arity o) → Bool) → Bool
  | _, none, _ => true
  | _, some (.iter _ _), a => a 0
  | _, some _, a => Finset.univ.sup a

private def flags : OrderedAlgebra explicitSig.sig where
  toAlgebra := { Carrier := fun _ => Bool, op := flagOp }
  order _ := inferInstance
  monotone_op o a b h := by
    cases o with
    | none => exact le_rfl
    | some o =>
      cases o
      case iter => exact h (0 : Fin 2)
      all_goals exact Finset.sup_mono_fun (fun j _ => h j)

private theorem fold_flag (i : TypingIndex τ) (a : explicitSig.syn.Carrier i) :
    explicitSig.eval flags.toAlgebra a = UB.fold flags.toAlgebra a := by
  have h := explicitSig.isInitial.hom_ext (explicitSig.isInitial.to flags.toAlgebra)
    (UB.foldHom flags.toAlgebra)
  exact congrArg (fun f => Algebra.Hom.map f a) h

private theorem flag_inherited {i : TypingIndex τ} (a : baseSig.syn.Carrier i) :
    explicitSig.eval flags.toAlgebra ((PSig.translate (UB.inclusion baseSig)).map a) = false := by
  let M := Algebra.reductObj (PSig.toSig (UB.inclusion baseSig)) flags.toAlgebra
  let f : baseSig.syn ⟶ M := {
    map := fun _ => false
    comm := fun o _ => by
      change false = flagOp (some o) (fun _ => false)
      cases o
      case iter => rfl
      all_goals exact ((Finset.sup_eq_bot_iff _ _).2 (fun _ _ => rfl)).symm }
  refine (baseSig.eval_reduct (UB.inclusion baseSig) flags.toAlgebra a).symm.trans ?_
  exact congrArg (fun g => Algebra.Hom.map g a) (baseSig.isInitial.hom_ext _ f)

private theorem flag_valid : flags ∈ (institution.obj explicitSig).modelsOf
    (UB.LetIter.explicitSpec alphabet Γ axioms).axioms := by
  intro s hs p hp
  rcases hs with ⟨s', _, rfl⟩ | ⟨i, a, rfl⟩
  · obtain ⟨⟨i, a, b⟩, _, rfl⟩ := List.mem_map.1 hp
    change @LE.le Bool _ (explicitSig.eval flags.toAlgebra ((PSig.translate (UB.inclusion baseSig)).map a))
      (explicitSig.eval flags.toAlgebra ((PSig.translate (UB.inclusion baseSig)).map b))
    rw [flag_inherited, flag_inherited]
  · obtain rfl := List.mem_singleton.1 hp
    change @LE.le Bool _ (explicitSig.eval flags.toAlgebra a)
      (explicitSig.eval flags.toAlgebra (UB.Expr.ub (i := i)))
    rw [fold_flag i (UB.Expr.ub (i := i))]
    exact le_top

example : ¬ (UB.LetIter.explicitOrder alphabet Γ axioms).Rel unfoldLoop loop := by
  intro h
  have hf := h flags flag_valid _ (List.mem_singleton_self _)
  have hu : explicitSig.eval flags.toAlgebra unfoldLoop = true := (fold_flag closed _).trans rfl
  have hl : explicitSig.eval flags.toAlgebra loop = false := (fold_flag closed _).trans rfl
  have hle : @LE.le Bool _ (explicitSig.eval flags.toAlgebra unfoldLoop)
      (explicitSig.eval flags.toAlgebra loop) := hf
  rw [hu, hl] at hle
  exact (by decide : ¬ true ≤ false) hle

#print axioms UB.LetIter.quotientIso
#print axioms UB.LetIter.preserves_native
#print axioms Silmaril.Isotope.Refinement.UB.no_literal_at_linear_state
#print axioms Silmaril.Isotope.Refinement.UB.iter_body_refines_literal

end LetIterUBRegression
