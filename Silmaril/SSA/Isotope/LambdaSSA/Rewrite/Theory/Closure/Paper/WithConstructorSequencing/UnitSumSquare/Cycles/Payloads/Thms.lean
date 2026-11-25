module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles

/-! # Uniformity for finite exit and recurrence tables with payload choices -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Termination (run forwardingRows)
open scoped Function Paper.BoundSimulation.Obstruction

/-- A successful run has a literal payload exactly when a visited row resets
it. The total successor repeats the exit row after termination. -/
theorem run_resets_iff {B A : Shape} (p : A.Row → OutputCode B A)
    {fuel : Nat} {i : A.Row} {o : StateCode B} (h : run p fuel i = some o) :
    o.payload = .literal ↔
      ∃ k < fuel, (p ((Cycles.Mixed.successor (fun j => (p j).tag))^[k] i)).payload = .literal :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.run_resets_iff p h

/-- A cut returning to its initial row has a literal payload exactly when
some row of that cycle resets it. -/
theorem cut_lap_resets_iff {B A : Shape} (p : A.Row → OutputCode B A) (mark : A.Row → Bool)
    {fuel : Nat} {i : A.Row} {m : Payload}
    (h : run (cutRows p mark) fuel i = some ⟨.inr i, m⟩) :
    m = .literal ↔ ResetsOnOrbit p i :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.cut_lap_resets_iff p mark h

/-- A cut returning to its initial row forwards exactly when the entire cycle forwards. -/
theorem cut_lap_forwards_iff {B A : Shape} (p : A.Row → OutputCode B A) (mark : A.Row → Bool)
    {fuel : Nat} {i : A.Row} {m : Payload}
    (h : run (cutRows p mark) fuel i = some ⟨.inr i, m⟩) :
    m = .forward ↔
      ∀ k, (p ((Cycles.Mixed.successor (fun v => (p v).tag))^[k] i)).payload = .forward :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.cut_lap_forwards_iff p mark h

/-- A bounded run has the same exit tag after changing only the payload actions. -/
theorem run_same_tag {B A : Shape} {p q : A.Row → OutputCode B A}
    (same : ∀ i, (p i).tag = (q i).tag) {n : Nat} {i : A.Row} {o : StateCode B}
    (hq : run q n i = some o) : ∃ mode, run p n i = some ⟨o.tag, mode⟩ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.run_same_tag same hq

/-- A singleton loop has the same iteration for either payload choice. -/
theorem iterate_selfStep (B : Shape) (m : Payload) :
    iterate (selfStep B m) = iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.iterate_selfStep B m

/-- A payload choice before the singleton nonexiting loop is absorbed. -/
theorem payload_before_self (B : Shape) (m : Payload) :
    Shape.unit.emit () m ≫ iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) =
      iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.payload_before_self B m

/-- The iteration of a nonexiting row is the singleton self-loop. -/
theorem iterate_nonexit_row (B A : Shape) (p : A.Row → OutputCode B A) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    A.inj i ≫ iterate (stepWithPayload B A p) =
      iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.iterate_nonexit_row B A p i infinite

/-- Uniformity for coded tables and coded state maps with either payload choice. -/
theorem iterate_case_uniformity (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ stepWithPayload B D q)) :
    iterate (stepWithPayload B A p) = caseMap A D rows ≫ iterate (stepWithPayload B D q) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.iterate_case_uniformity B A D rows p q comm

/-- The same uniformity along explicit projected table representatives. -/
theorem iterate_projected_case_uniformity (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A p))
    (hg : projection.map g = projection.map (stepWithPayload B D q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ g)) :
    projection.map (iterate f) =
      projection.map (caseMap A D rows) ≫ projection.map (iterate g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.iterate_projected_case_uniformity
    B A D rows p q hf hg comm

namespace ResetCycle

open Cycles.Mixed.MergeCycle (result source target tags)
local notation "rows" => forwardingRows tags

/-- A forwarding state map merges a resetting cycle and keeps the exiting path. -/
theorem projected_square :
    projection.map (stepWithPayload result source sourceSteps ≫
        coprod.map (𝟙 (obj result.ty)) (caseMap source target rows)) =
      projection.map (caseMap source target rows ≫ stepWithPayload result target targetSteps) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.ResetCycle.projected_square

/-- One lap of the alternating cycle accumulates literal unit. -/
theorem resetting_lap :
    run (cutRows sourceSteps mark) 2 (.inl (.inl ())) = some ⟨.inr (.inl (.inl ())), .literal⟩ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.ResetCycle.resetting_lap

/-- The terminating path retains the earlier reset through its forwarding exit. -/
theorem reset_then_exit :
    run sourceSteps 2 (.inr (.inl ())) = some ⟨(), .literal⟩ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.ResetCycle.reset_then_exit

/-- The state map identifies distinct cycle rows. -/
theorem not_mono : ¬ Mono (caseMap source target rows) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.ResetCycle.not_mono

/-- The four-to-three iteration equation holds in standard Paper. -/
theorem iterate_merge :
    iterate (stepWithPayload result source sourceSteps) =
      caseMap source target rows ≫ iterate (stepWithPayload result target targetSteps) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles.ResetCycle.iterate_merge

end ResetCycle

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads
