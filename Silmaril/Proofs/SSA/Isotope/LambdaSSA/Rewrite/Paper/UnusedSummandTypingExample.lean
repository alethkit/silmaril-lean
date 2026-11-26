module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Readback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms

/-! # Two live labels with heterogeneous common payloads -/

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnusedSummandFixture

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical Semantics.Categorical.UnusedSummand
open Extension.Singleton Extension.Singleton.StructuralValues

private inductive Op where
  | poll

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Flag : Ty Empty := Silmaril.coprod U U

instance : HasTy Op (Ty Empty) where
  src _ := U
  trg _ := Flag

instance : HasEff Op Bool := ⟨fun _ => true⟩

private def payloads : Fin 2 → Ty Empty := Fin.cases U (fun _ => Flag)
private def emptyLeft : Fin 2 → Ty Empty := Fin.cases .empty (fun _ => U)
private def emptyRight : Fin 2 → Ty Empty := Fin.cases U (fun _ => .empty)

private def first : Row (Φ := Op) payloads [U] [Flag] :=
  .case (.op .poll .unit)
    (.jump 1 (.var 1 rfl))
    (.exit 0 rfl (.var 0 rfl))

private def second : Row (Φ := Op) payloads [U] [Flag] := .jump 0 .unit

private def table : Program (Φ := Op) payloads [U] [Flag] where
  entry := .jump 0 .unit
  blocks := Fin.cases first (fun _ => second)

/-- The selected poll reply either transfers to the second label with the
retained flag, or returns the reply. The second label transfers back. -/
example :
    table.region true =
      .cfg (.br 0 (.inl .unit)) 2
        (Fin.cases (.case (.op .poll .unit)
          (.br 1 (.inl (.var 2))) (.br 2 (.var 0)))
          (fun _ => .br 0 (.inl .unit))) := by
  unfold Program.region table
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

example : (table.region true).HasType [Flag] [U] := table.hasType (some emptyLeft)
example : (table.region true).HasType [Flag] [U] := table.hasType (some emptyRight)

private theorem covers : table.targetsEveryLabel := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .inl rfl
  · obtain rfl := Fin.eq_zero j
    exact .inr ⟨0, .inl rfl⟩

private def sparse : Program (Φ := Op) payloads [U] [Flag] where
  entry := .jump 0 .unit
  blocks _ := .exit 0 rfl .unit

/-- An untargeted label can have a type outside the widened family. -/
private def sparseFamily : Fin 2 → Ty Empty := Fin.cases (Silmaril.coprod U .empty) (fun _ => U)

private theorem sparseFamily_outside (D : Fin 2 → Ty Empty) :
    sparseFamily ≠ family payloads (some D) := by
  intro eq
  have chosen := congrFun eq (1 : Fin 2)
  change Ty.unit = Ty.coprod Flag (D 1) at chosen
  cases chosen

private theorem sparse_not_covered : ¬ sparse.targetsEveryLabel := by
  intro coverage
  rcases coverage 1 with h | ⟨_, h⟩
  · have neq : (0 : Fin 2) ≠ 1 := by decide
    exact neq h
  · exact False.elim h

local notation "Seed" => WithCaseReturns.BinaryFold.JoinedStep (τ := Ty Empty) (Φ := Op) true
local notation "inc" => inclusion Seed
local notation "model" => typeModel Seed

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive guardedIteration guardedElgot
attribute [local instance] Extension.Singleton.StructuralValues.hasFiniteCoproducts

private theorem chosenRolling : IterationRolling (Extension.Singleton.TypeCategory Seed) :=
  fun h step => iterateChosen_roll Seed h step

/-- These are exact graph witnesses for two distinct widened families of the
same raw CFG, and for its common-family rendering. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∃ f, RegionDenotes inc model (table.hasType none) f ∧
      RegionDenotes inc model (table.hasType (some emptyLeft)) f ∧
      RegionDenotes inc model (table.hasType (some emptyRight)) f := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  obtain ⟨f, agrees⟩ := table.denotes_agree inc model chosenRolling
  exact ⟨f, agrees none, agrees (some emptyLeft), agrees (some emptyRight)⟩

/-- The two-label comparison consumes independently quantified exact graph
witnesses, with no family supplied to the proof by the caller. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f g}, RegionDenotes inc model (table.hasType (some emptyLeft)) f →
      RegionDenotes inc model (table.hasType (some emptyRight)) g → f = g := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  intro f g d e
  exact table.denotes_eq inc model chosenRolling covers d e

/-- The same top-level inversion also compares a widened witness with an
arbitrary witness of the common rendering. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f g}, RegionDenotes inc model (table.hasType (some emptyLeft)) f →
      RegionDenotes inc model (table.hasType none) g → f = g := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  intro f g d e
  exact table.denotes_eq inc model chosenRolling covers d e

/-- The graph really admits an internal family outside the widened shape
when label 1 has no written incoming jump. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ¬ sparse.targetsEveryLabel ∧
    ∃ f : (inc).obj (ctxObj model [Flag]) ⟶ (inc).obj (labelObj model [U]),
      CfgDenotesAt inc model sparseFamily (sparse.entry.region true id)
        (fun i => (sparse.blocks i).region true Nat.succ) f ∧
      ∀ D, sparseFamily ≠ family payloads (some D) := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  have he : (sparse.entry.region true id).HasType [Flag] (List.ofFn sparseFamily ++ [U]) :=
    .br rfl (.inl .unit)
  have hb (i : Fin 2) :
      ((sparse.blocks i).region true Nat.succ).HasType (sparseFamily i :: [Flag])
        (List.ofFn sparseFamily ++ [U]) := .br rfl .unit
  obtain ⟨f, w⟩ := CfgDenotesAt.exists_of_typing inc model sparseFamily he hb
  exact ⟨sparse_not_covered, f, w, sparseFamily_outside⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnusedSummandFixture
