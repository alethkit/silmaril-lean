module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Extensions.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFreeITreeReflection
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns

/-! # The original term-case witness and the remaining pair kernel -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFreeITreeExtensions

open CategoryTheory
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory Paper.TypeCategory.ITree.Reflection
open Semantics.Interaction Semantics.Interaction.Typed
open Semantics (extend)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree
open CfgEta.TypeCategory (returnRegion returnRegion_typed returnRegion_branchValue caseValueBranches)

private theorem caseEqOf
    (Seed : VCtx (Ty Atom) → Region Op → Region Op → LCtx (Ty Atom) → Prop)
    (includeCase : ∀ {Γ r s L}, Paper.WithCaseReturns.Step false Γ r s L → Seed Γ r s L) :
    Paper.Extension.Eqv Seed [Input] termCase regionCase [Output] := by
  have hleft : Tm.BranchValue [payload] (.inr (.var 0) : Tm Op) Output := .inr (.var rfl)
  have hright : Tm.BranchValue [payload] (.inl (.var 0) : Tm Op) Output := .inl (.var rfl)
  let a : Tm Op := .inr (.var 0)
  let b : Tm Op := .inl (.var 0)
  have ha : Tm.HasType [payload] a Output := hleft.hasType
  have hb : Tm.HasType [payload] b Output := hright.hasType
  have pa : Tm.Pure false a := .inr .var
  have pb : Tm.Pure false b := .inl .var
  have hc := Paper.WithCaseReturns.Step.split ha hb pa pb
  have hl : Tm.BranchValue [payload, Output] (.inr (.var 0) : Tm Op) Output := .inr (.var rfl)
  have hr : Tm.BranchValue [payload, Output] (.inl (.var 0) : Tm Op) Output := .inl (.var rfl)
  have ht : Tm.HasType [Output] (.case (.var 0) (.inr (.var 0)) (.inl (.var 0)) : Tm Op) Output :=
    .case (.var rfl) hl.hasType hr.hasType
  have mid := caseValueBranches (returnRegion_typed ha) (returnRegion_typed hb)
  have e := Paper.Extension.Eqv.extra (returnRegion_typed ht).hasType mid.hasType (includeCase hc)
  have narrowed : Paper.Extension.Eqv Seed [Output]
      (.let₁ (.case (.var 0) (.inr (.var 0)) (.inl (.var 0))) (.br 0 (.var 0)))
      (.case (.var 0) (.br 0 (.inr (.var 0))) (.br 0 (.inl (.var 0)))) [Output] :=
    e.trans (.paper (.case (.var rfl)
      (.cfgEta (.native (.base (returnRegion_branchValue hl))))
      (.cfgEta (.native (.base (returnRegion_branchValue hr))))))
  have poll : ValueBranches [payload, Input] pollRegion [Output] :=
    .let₁ (.op (.var rfl)) (.br rfl (.var rfl))
  exact .case (.var rfl) (narrowed.renameVars ((Ren.wk [] Input).lift Output)) (.refl poll.hasType)

theorem caseOnly :
    Paper.Extension.Eqv (Paper.WithCaseReturns.Step false) [Input] termCase regionCase [Output] :=
  caseEqOf _ id

theorem caseJoined :
    caseProjection.map termArrow = caseProjection.map regionArrow :=
  (Paper.Extension.Singleton.ofRegion_eq_iff _ termCase_typed regionCase_typed).2 (caseEqOf _ Or.inr)

section Observer

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Env EnvTy Result)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
  (joined_same caseReturnJoin_same)
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit
open scoped Paper.BoundSimulation.Obstruction

private def inputEnv : Env := extend (fun _ => .unit) (.inl (.inl .unit))

private theorem inputEnv_typed : EnvTy [Input] inputEnv := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inl (.inl .base)
  | succ i => simp [At] at hi

theorem projectionUnitDistinct :
    projectionUnit.map termArrow ≠ projectionUnit.map regionArrow := by
  intro eq
  have rel := (Paper.Extension.Singleton.ofRegion_eq_iff _ termCase_typed regionCase_typed).1 eq
  have seen := joined_same (observation := { caseTerm := true }) rel inputEnv inputEnv_typed
  change Result.fault = .jump 0 (.inr .unit) at seen
  cases seen

theorem pairsDistinct :
    caseProjection.map nestedPairArrow ≠ caseProjection.map plainPairArrow := by
  intro eq
  have rel := (Paper.Extension.Singleton.ofRegion_eq_iff _ nestedPair_typed plainPair_typed).1 eq
  have seen := caseReturnJoin_same (observation := { pairLet := true }) rfl rel inputEnv inputEnv_typed
  change Result.fault = .jump 0 (.inl .unit) at seen
  cases seen

end Observer

theorem pairsSameImage :
    interpretation.map nestedPairArrow = interpretation.map plainPairArrow := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.hom_ext
  intro a
  change run nestedPairArrow a = run plainPairArrow a
  cases a with
  | inr n =>
    have left := SingletonFreeITreeReflection.run_eq_of_encoded nestedPair_typed (.inr n) (behavior (.inr n))
      (by simp [nestedPair, pollRegion, region, term, encodeValue, extend, raw, behavior, vis_bind, -bind_pure_comp])
    have right := SingletonFreeITreeReflection.run_eq_of_encoded plainPair_typed (.inr n) (behavior (.inr n))
      (by simp [plainPair, pollRegion, region, term, encodeValue, extend, raw, behavior, vis_bind, -bind_pure_comp])
    exact left.trans right.symm
  | inl b =>
    have left := SingletonFreeITreeReflection.run_eq_of_encoded nestedPair_typed (.inl b) (pure b)
      (by simp [nestedPair, region, term, encodeValue, extend])
    have right := SingletonFreeITreeReflection.run_eq_of_encoded plainPair_typed (.inl b) (pure b)
      (by simp [plainPair, region, term, encodeValue, extend])
    exact left.trans right.symm

section Descent

open Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open scoped MonoidalCategory

attribute [local instance] typeModel categoricalInstructions

theorem image_eq_of_caseProjection_eq {A B : Ty Atom} (f g : ofType (Φ := Op) A ⟶ ofType B)
    (h : caseProjection.map f = caseProjection.map g) : interpretation.map f = interpretation.map g := by
  obtain ⟨p, hp, rfl⟩ := exists_ofRegion f
  obtain ⟨q, hq, rfl⟩ := exists_ofRegion g
  have eq := (Paper.Extension.Singleton.ofRegion_eq_iff _ hp hq).1 h
  let J := typeJ (m := TreeModel)
  let M := ofMonadicTypeModel (τ := Ty Atom)
  have := regionTypingCoherent raw compatible
  have denoted := Paper.WithCaseReturns.Eqv.sound false J M (fun _ _ => ⟨rfl, rfl⟩)
    eq hp.hasType hq.hasType
  unfold interpretation
  rw [weakITreeFunctor_map_ofRegion, weakITreeFunctor_map_ofRegion]
  unfold denoteSingletonRegion
  rw [denoted]

end Descent

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFreeITreeExtensions
