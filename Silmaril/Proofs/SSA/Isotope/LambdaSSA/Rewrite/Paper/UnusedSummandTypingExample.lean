module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Thms
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

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnusedSummandFixture
