module

import Silmaril.Courses.Cambridge.L1.OperationalInstitution
import Silmaril.Courses.Cambridge.L2.OperationalInstitution

/-! Checked examples of store effects, signature reducts, and finite runs. -/

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Operational
open Silmaril.Courses.Cambridge

private def initialStore : L1.Store := L1.Store.empty.insert "x" 7
private def updatedStore : L1.Store := initialStore.insert "x" 42

private def l1Start : L1.Config := ⟨.assign "x" (.int 42), initialStore⟩
private def l1Result : L1.Config := ⟨.skip, updatedStore⟩

private theorem assignStep : L1.Step l1Start l1Result :=
  .assignValue (by simp [initialStore])

example : (Signature.institution.obj L1.OperationalInstitution.system.shape).Sat
    (Discrete.mk L1.OperationalInstitution.system.model) (l1Start, (), l1Result) :=
  (L1.OperationalInstitution.sat_iff _ _).2 assignStep

example : L1.OperationalInstitution.semantics.May l1Start (.returned l1Result) ∧
    L1.Store.lookup l1Result.store "x" = some 42 := by
  refine ⟨(L1.OperationalInstitution.may_return_iff _ _).2 ⟨.single assignStep, .skip⟩, ?_⟩
  simp [l1Result, updatedStore]

-- Fixing the store in a smaller signature gives exactly the store-preserving edges there.
private def expressions : Signature := ⟨L1.Expr, Unit⟩
private def fixedStore : expressions ⟶ L1.OperationalInstitution.system.shape :=
  ⟨fun e => ⟨e, initialStore⟩, id⟩

private theorem fixedStoreDeref : (Signature.institution.obj expressions).Sat
    ((Signature.institution.map fixedStore).mod.obj
      (Discrete.mk L1.OperationalInstitution.system.model)) (.deref "x", (), .int 7) := by
  erw [OperationalInstitution.model_reduct L1.lts fixedStore]
  exact L1.Step.deref (by simp [initialStore])

example : (Signature.institution.obj L1.OperationalInstitution.system.shape).Sat
    (Discrete.mk L1.OperationalInstitution.system.model)
    ((Signature.institution.map fixedStore).sen (.deref "x", (), .int 7)) :=
  (satisfaction_condition Signature.institution fixedStore _ _).2 fixedStoreDeref

example (t : L1.Config) : ¬ (Signature.institution.obj L1.OperationalInstitution.system.shape).Sat
    (Discrete.mk L1.OperationalInstitution.system.model) (⟨.deref "x", L1.Store.empty⟩, (), t) := by
  intro h
  have step := (L1.OperationalInstitution.sat_iff _ _).1 h
  cases step with
  | deref present => simp at present

private def l2Start : L2.Config := ⟨.app (.lam .int (.bvar 0)) (.deref "x"), updatedStore⟩
private def l2Ready : L2.Config := ⟨.app (.lam .int (.bvar 0)) (.int 42), updatedStore⟩
private def l2Result : L2.Config := ⟨.int 42, updatedStore⟩

private theorem argumentStep : L2.Step l2Start l2Ready :=
  .appRight (.lam _ _) (.deref (by simp [updatedStore]))

private theorem betaStep : L2.Step l2Ready l2Result :=
  .appFun (.int 42)

private theorem l2Run : Runs L2.OperationalInstitution.system.model l2Start [(), ()] l2Result :=
  .stepL argumentStep (.stepL betaStep .refl)

example : L2.OperationalInstitution.semantics.May l2Start (.returned l2Result) :=
  (L2.OperationalInstitution.may_return_iff _ _).2
    ⟨L2.steps_iff_reachable.2 ⟨_, l2Run⟩, .int 42⟩

example : (Signature.institution.obj L2.OperationalInstitution.system.shape).Sat
    (Discrete.mk L2.OperationalInstitution.system.model) (l2Ready, (), l2Result) :=
  (L2.OperationalInstitution.sat_iff _ _).2 betaStep

example : ¬ L2.OperationalInstitution.semantics.May l2Start .trap := by
  rintro ⟨_, _, _, h⟩
  cases h
