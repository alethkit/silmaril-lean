module

import Silmaril.SSA.Isotope.Institution.Parallel.Inclusions.Thms
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Control.Monad.Writer

open Silmaril Silmaril.Isotope Silmaril.Isotope.Institution Silmaril.Logic.Institution
open Silmaril.Isotope.Parallel Silmaril.Isotope.Parallel.Institution Semantics CategoryTheory

private abbrev TyCode := Ty Unit
private abbrev D := Ty.denote (fun _ : Unit => Nat)
private abbrev Γ : Ctx Empty TyCode := .nil
private abbrev number : TyCode := .base ()

private def dialect : InstrSig TyCode Bool where
  Instr := Bool
  hasTy := ⟨fun _ => .unit, fun _ => number⟩
  hasEff := ⟨fun _ => true⟩

private def extended : InstrSig TyCode Bool where
  Instr := Option Bool
  hasTy := ⟨(fun | some _ => .unit | none => number),
    (fun | some _ => number | none => .unit)⟩
  hasEff := ⟨Option.isSome⟩

/-- Exchange the two names and include them in a larger alphabet. -/
private def renameOp : dialect ⟶ extended :=
  ⟨fun b => some (!b), fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

private def emit (b : Bool) : LetPar.Tm Empty dialect.Instr 0 := .op b .unit

private def emitD (b : Bool) : Derivation dialect.Instr Γ .nil (emit b) number := .op .unit

private def swapTest : Equation dialect .seq Γ :=
  ⟨0, .nil, product number number, (Tm.par (emit false) (emit true)).swap,
    .par (emit true) (emit false),
    .let₂ (.par (emitD false) (emitD true)) (.pair .bv .bv), .par (emitD true) (emitD false)⟩

private abbrev trace := Writer (FreeMonoid Nat)

private def tag (b : Bool) : Nat := if b then 2 else 7

private def sortedLog : ParOp trace := fun a b =>
  let log := if a.run.2.toList.headD 0 ≤ b.run.2.toList.headD 0 then
    a.run.2 * b.run.2
  else b.run.2 * a.run.2
  WriterT.mk ((a.run.1, b.run.1), log)

private def orderedLog : ParOp trace := fun a b => do
  let x ← a
  let y ← b
  pure (x, y)

private def traceModel (par : ParOp trace) : Model D extended where
  M := trace
  par := par
  instr := ⟨fun
    | some b, _ => WriterT.mk (tag b, FreeMonoid.of (tag b))
    | none, _ => pure PUnit.unit⟩

private def I := LetPar.observation (ε := Bool) Γ D

private abbrev noFree : FreeEnv D Γ := fun x => nomatch x
private abbrev noBound : BoundEnv D .nil := fun i => Fin.elim0 i

example : LetPar.Equiv false Γ swapTest.bound swapTest.left swapTest.right swapTest.result :=
  Parallel.Equiv.parSwap ⟨emitD false⟩ ⟨emitD true⟩

example :
    LetPar.Equiv false Γ (swapTest.map renameOp).bound
      (swapTest.map renameOp).left (swapTest.map renameOp).right (swapTest.map renameOp).result :=
  LetPar.mapInstr_equiv renameOp (Parallel.Equiv.parSwap ⟨emitD false⟩ ⟨emitD true⟩)

private theorem sorted_satisfies :
    (I.obj extended).Sat (traceModel sortedLog) ((I.map renameOp).sen swapTest) := by
  intro γ ρ
  rfl

example : ¬ (I.obj extended).Sat (traceModel orderedLog) ((I.map renameOp).sen swapTest) := by
  intro h
  have he := h noFree noBound
  have log := congrArg (fun (x : trace (Nat × Nat)) => x.run.2.toList) he
  change [2, 7] = [7, 2] at log
  cases log

/-- This is actual restriction of the larger alphabet, including the exchange of the two names. -/
private def reducedEval : trace Nat :=
  ((traceModel orderedLog).reduct renameOp).instr.eval (false : dialect.Instr) PUnit.unit

example : reducedEval.run.1 = 2 := rfl

example : (I.obj dialect).Sat ((I.map renameOp).mod.obj (traceModel sortedLog)) swapTest :=
  ((I.map renameOp).sat (traceModel sortedLog) swapTest).mp sorted_satisfies

private def orderTest : Equation dialect .seq Γ :=
  ⟨0, .nil, product number number, swapTest.right, .pair (emit true) (emit false),
    swapTest.rhs, .pair (emitD true) (emitD false)⟩

/-- In the same model, ordinary pairs retain left-to-right sequencing. -/
example : ¬ (I.obj extended).Sat (traceModel sortedLog) ((I.map renameOp).sen orderTest) := by
  intro h
  have log := congrArg (fun (x : trace (Nat × Nat)) => x.run.2.toList) (h noFree noBound)
  change [2, 7] = [7, 2] at log
  cases log

private def noLogs : Model D extended where
  M := Id
  par := fun a b => (a, b)
  instr := ⟨fun
    | some b, _ => tag b
    | none, _ => PUnit.unit⟩

private def eraseLog : Model.Hom (traceModel sortedLog) noLogs where
  app {A} x := (show trace A from x).run.1
  monadHom := Cslib.IsMonadHom.mk' (fun _ => rfl) (fun _ _ => rfl)
  map_par _ _ := rfl
  map_instr p _ := by cases p <;> rfl

example : ((Model.reductFunctor renameOp).map eraseLog :
    (traceModel sortedLog).reduct renameOp ⟶ noLogs.reduct renameOp).app
      (WriterT.mk (42, FreeMonoid.of 7) : trace Nat) = (42 : Nat) :=
  rfl

private abbrev caseEnabled := LetParCase.hasCase

private def chosen : LetParCase.Tm Empty dialect.Instr 0 :=
  .case caseEnabled (.inl caseEnabled .unit) (.op false (.bv 0)) (.op true (.bv 0))

private def chosenD : Derivation dialect.Instr Γ .nil chosen number :=
  .case (A := Ty.unit) (B := Ty.unit) (.inl .unit) (.op .bv) (.op .bv)

private def sibling := LetParCase.ofLetPar (emit true)
private def siblingD := LetParCase.ofLetParDerivation (emitD true)

private def distributionTest : Equation dialect .case Γ :=
  ⟨0, .nil, product number number, .par chosen sibling,
    .case caseEnabled (.inl caseEnabled .unit)
      (.par (.op false (.bv 0)) sibling.lift) (.par (.op true (.bv 0)) sibling.lift),
    .par chosenD siblingD,
    .case (A := Ty.unit) (B := Ty.unit) (.inl .unit) (.par (.op .bv) (siblingLiftD Ty.unit))
      (.par (.op .bv) (siblingLiftD Ty.unit))⟩
where
  siblingLiftD (A : TyCode) : Derivation dialect.Instr Γ (.snoc .nil A) sibling.lift number := .op .unit

private def J := LetParCase.observation (ε := Bool) Γ D

example : LetParCase.Equiv false Γ (distributionTest.map renameOp).bound
    (distributionTest.map renameOp).left (distributionTest.map renameOp).right
    (distributionTest.map renameOp).result :=
  LetParCase.mapInstr_equiv renameOp
    (LetParCase.parCaseLeft (X := Ty.unit) (Y := Ty.unit) (.inl .unit)
      ⟨.inl .unit⟩ ⟨.op .bv⟩ ⟨.op .bv⟩ ⟨siblingD⟩)

example : (J.obj extended).Sat (traceModel orderedLog) ((J.map renameOp).sen distributionTest) := by
  intro γ ρ
  rfl

example : (J.obj extended).Sat (traceModel sortedLog)
    (((letParCaseInclusion (ε := Bool) Γ D).ρ.app extended).sen ((I.map renameOp).sen swapTest)) :=
  ((letParCaseInclusion (ε := Bool) Γ D).ρ.app extended).sat (traceModel sortedLog)
    ((I.map renameOp).sen swapTest) |>.mpr sorted_satisfies

private def seqEmit : LetSeq.LocallyNameless.Derivation dialect.Instr Γ .nil
    (.op false .unit) number := .op .unit

private def seqLetEmit : LetSeq.LocallyNameless.Derivation dialect.Instr Γ .nil
    (.let₁ .unit (.op false (.bv 0))) number := .let₁ .unit (.op .bv)

example : (I.obj dialect).Sat ((traceModel sortedLog).reduct renameOp)
    (Equation.ofLetSeq seqEmit seqLetEmit) :=
  (Equation.ofLetSeq_sat seqEmit seqLetEmit _).mpr (by intro γ ρ; rfl)

private def caseEmit : LetCase.LocallyNameless.Derivation dialect.Instr Γ .nil
    (.op false .unit) number := .op .unit

private def caseChoose : LetCase.LocallyNameless.Derivation dialect.Instr Γ .nil
    (.case (.inl .unit) (.op false (.bv 0)) (.op true (.bv 0))) number :=
  .case (A := Ty.unit) (B := Ty.unit) (.inl .unit) (.op .bv) (.op .bv)

example : (J.obj dialect).Sat ((traceModel sortedLog).reduct renameOp)
    (Equation.ofLetCase caseEmit caseChoose) :=
  (Equation.ofLetCase_sat caseEmit caseChoose _).mpr (by intro γ ρ; rfl)

#print axioms Silmaril.Isotope.LetPar.observation
#print axioms Silmaril.Isotope.LetParCase.observation
#print axioms Silmaril.Isotope.LetPar.mapInstr_equiv
#print axioms Silmaril.Isotope.LetParCase.mapInstr_equiv
#print axioms Silmaril.Isotope.Parallel.Institution.denote_mapInstr
#print axioms Silmaril.Isotope.Parallel.Institution.Model.reductFunctor_comp
#print axioms Silmaril.Isotope.Parallel.Institution.denote_hom
#print axioms Silmaril.Isotope.Parallel.Institution.letParCaseInclusion
#print axioms Silmaril.Isotope.Parallel.Institution.Equation.ofLetSeq_sat
#print axioms Silmaril.Isotope.Parallel.Institution.Equation.ofLetCase_sat
