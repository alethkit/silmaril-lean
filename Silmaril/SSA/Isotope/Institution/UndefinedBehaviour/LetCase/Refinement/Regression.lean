module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetCase.Model.Thms

/-! The native case-beta rule can remove the only occurrence of UB in a
literal-unit term. The ground extension of the old refinement theory
does not reflect that rule. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Institution Silmaril.Isotope.Institution.Refinement
open Silmaril.Isotope.LetCase.LocallyNameless
open Silmaril.Isotope.Theory (TypingIndex)

namespace LetCaseUBRefinementRegression

attribute [local instance] UB.dialectTyping

private abbrev τ := Ty Empty

private def alphabet : InstrSig τ Bool where
  Instr := Empty
  hasTy := ⟨Empty.elim, Empty.elim⟩
  hasEff := ⟨Empty.elim⟩

private abbrev Γ : Ctx Empty τ := .nil
private abbrev closed : TypingIndex τ := ⟨0, .nil, unit⟩

private abbrev S := (casePSig alphabet.Instr Γ).sig

private def unitAt {n : Nat} (β : BoundCtx τ n) :
    UB.LetCase.Explicit alphabet Γ ⟨n, β, unit⟩ :=
  UB.Expr.node (S := S) (Models.Operation.unit (β := β)) (fun j => Fin.elim0 j)

private def inactiveUB : UB.LetCase.Explicit alphabet Γ closed :=
  let scrutinee := UB.Expr.node (S := S) (Models.Operation.inl (β := .nil) unit unit)
    (fun _ => by
      change UB.LetCase.Explicit alphabet Γ ⟨0, .nil, unit⟩
      exact unitAt .nil)
  let op : S.Op closed := Models.Operation.case (β := .nil) unit unit unit
  UB.Expr.node op (Fin.cases (motive := fun j => UB.Expr S (S.argSort op j))
    (by exact scrutinee)
    (Fin.cases (motive := fun j : Fin 2 => UB.Expr S (S.argSort op j.succ))
      (by exact unitAt (.snoc .nil unit)) (fun _ => UB.Expr.ub)))

private def reduced : UB.LetCase.Explicit alphabet Γ closed :=
  let op : S.Op closed := Models.Operation.let₁ (β := .nil) unit unit
  UB.Expr.node op (Fin.cases (motive := fun j => UB.Expr S (S.argSort op j))
    (by exact unitAt .nil) (fun _ => by exact unitAt (.snoc .nil unit)))

private abbrev R : TypedRelation Empty alphabet.Instr τ := fun _ _ _ _ => False
private abbrev axioms := (caseTheory false Γ R).sentences

example : UB.LetCase.nativeRefines alphabet true false Γ R
    (UB.LetCase.encode alphabet true Γ inactiveUB) (UB.LetCase.encode alphabet true Γ reduced) := by
  let := (UB.dialect alphabet true).hasEff
  exact .equiv (.ax (.structural (.caseBetaL .unit .unit (.op (Sum.inr unit) .unit)))
    (.case (A := unit) (B := unit) (.inl .unit) .unit (.op .unit)) (.let₁ .unit .unit))

example : ¬ (UB.LetCase.explicitOrder alphabet Γ axioms).Rel inactiveUB reduced := by
  intro h
  have hn := (UB.LetCase.refinement_iff (e := true) axioms inactiveUB reduced).1 h
  have hv := hn _ (UB.LetCase.flagModel_valid (e := true) axioms) _ (List.mem_singleton_self _)
  exact (by decide : ¬ true ≤ false) hv

example :
    (UB.adjoin (casePSig alphabet.Instr Γ)).eval
      (UB.LetCase.explicitModel alphabet true Γ (UB.LetCase.flagModel alphabet true Γ)).toAlgebra
      inactiveUB = ULift.up true :=
  (UB.LetCase.encode_eval (UB.LetCase.flagModel alphabet true Γ) inactiveUB).symm.trans rfl

#print axioms UB.LetCase.quotientIso
#print axioms UB.LetCase.preserves_native
#print axioms UB.LetCase.encode_eval
#print axioms UB.LetCase.flagModel_valid

end LetCaseUBRefinementRegression
