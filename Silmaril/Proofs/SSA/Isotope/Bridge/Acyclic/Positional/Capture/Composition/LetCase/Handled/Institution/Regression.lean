module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model)
open Silmaril.Logic.ITree.TraceInstitution (allRepliesModel)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation numberGrammar readGrammar grammarCase)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.Structural.Finite (StructuralContext)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open LetSeq.StraightLine.Structural (Log)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## Three handled-trace models over the free requests -/

private abbrev allReplies : HandledModel Op := allRepliesModel (events Op)
private abbrev scriptedModel : HandledModel Op := ⟨Log Empty Op, fun _ => True, scripted Op⟩
private abbrev alternatingModel : HandledModel Op := ⟨Bool, fun _ => True, alternating⟩

example : Exposing allReplies ∧ Exposing scriptedModel :=
  ⟨allReplies_exposing, exposing_of_exposes scripted_exposes⟩

/-- The state-flipping model cannot replay the history that repeats a reply. -/
example : ¬ Exposing alternatingModel := fun exposing => by
  obtain ⟨state, -, _, first, _, second, -⟩ := exposing repeated finish
  have flipped : state = !state := by
    rw [first.2] at second
    exact first.1.symm.trans second.1
  cases state <;> cases flipped

/-! ## The directed sentence between the two composites -/

/-- The existing typed LetCase equation between the two composites. -/
private abbrev composites : CaseEquation (sig Op) :=
  captured (Case.seq route route) (Case.seq route echo)

example : swap composites = captured (Case.seq route echo) (Case.seq route route) := rfl

/-- The models that replay every history reject it in both directions. -/
example : ¬ SatLe allReplies composites ∧ ¬ SatLe allReplies (swap composites) ∧
    ¬ SatLe scriptedModel composites ∧ ¬ SatLe scriptedModel (swap composites) :=
  ⟨fun holds => native_differ (Quotient.sound ((satLe_iff_equiv input allReplies_exposing _ _).mp holds)),
    fun holds => native_differ (Quotient.sound ((satLe_iff_equiv input allReplies_exposing _ _).mp holds)).symm,
    fun holds => native_differ
      (Quotient.sound ((satLe_iff_equiv input (exposing_of_exposes scripted_exposes) _ _).mp holds)),
    fun holds => native_differ
      (Quotient.sound ((satLe_iff_equiv input (exposing_of_exposes scripted_exposes) _ _).mp holds)).symm⟩

/-- So the sentence is not valid in all handled models. -/
example : ¬ ∀ M : HandledModel Op, SatLe M composites :=
  fun valid => native_differ (Quotient.sound ((valid_iff_equiv input _ _).mp valid))

/-- The state-flipping model satisfies it in both directions. Satisfaction
in one fixed policy does not give native equality. -/
private theorem alternating_satisfies : SatLe alternatingModel composites ∧ SatLe alternatingModel (swap composites) :=
  ⟨(satLe_iff_refines alternating (Case.seq route route) (Case.seq route echo)).mpr fun w state => by
      rw [run_twice, run_crossed]
      exact (alternating_collapses state w.1 w.2).1,
    (satLe_iff_refines alternating (Case.seq route echo) (Case.seq route route)).mpr fun w state => by
      rw [run_twice, run_crossed]
      exact (alternating_collapses state w.1 w.2).2⟩

example : SatLe alternatingModel composites ∧ ¬ both = mixed := ⟨alternating_satisfies.1, native_differ⟩

/-! ## The same sentence through readback and emission -/

/-- The ranked sentence built by the checked readback of the composites. -/
private abbrev numbered : RankedEquation (sig Op) :=
  numberGrammar (grammarOf nonempty (Case.seq route route) (Case.seq route echo))

example : numbered = rankedOf (CheckedTable.ofLetCase nonempty (Case.seq route route).2)
    (CheckedTable.ofLetCase nonempty (Case.seq route echo).2) :=
  numberGrammar_grammarOf nonempty _ _

/-- Satisfaction of the ranked sentence is satisfaction of the LetCase
sentence, in each of the three models. -/
example : (rankedRoom Op).Sat ⟨alternatingModel⟩ numbered ∧ ¬ (rankedRoom Op).Sat ⟨allReplies⟩ numbered ∧
    ¬ (rankedRoom Op).Sat ⟨scriptedModel⟩ numbered :=
  ⟨(sat_readback nonempty _ _ ⟨alternatingModel⟩).mpr alternating_satisfies.1,
    fun holds => native_differ (Quotient.sound ((satLe_iff_equiv input allReplies_exposing _ _).mp
      ((sat_readback nonempty _ _ ⟨allReplies⟩).mp holds))),
    fun holds => native_differ (Quotient.sound
      ((satLe_iff_equiv input (exposing_of_exposes scripted_exposes) _ _).mp
        ((sat_readback nonempty _ _ ⟨scriptedModel⟩).mp holds)))⟩

/-- Emitting the numbered sentence again does not change satisfaction. -/
example (N : (grammarRoom Op).Mod) :
    (grammarRoom Op).Sat N (readGrammar numbered) ↔
      (grammarRoom Op).Sat N (grammarOf nonempty (Case.seq route route) (Case.seq route echo)) :=
  sat_read_number N _

/-! ## The hom order of the semantic functors is satisfaction -/

private def written : Interface Op captures input := ⟨exits, nonempty⟩
private def graph (p : CheckedTable Op Source exits) : written ⟶ written := Quotient.mk _ p

private def routeGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty route.2
private def echoGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty echo.2

example : (handledFunctor (model Op) alternating input).map both ≤
    (handledFunctor (model Op) alternating input).map mixed ↔ (caseRoom Op).Sat ⟨alternatingModel⟩ composites :=
  handledFunctor_map_le_iff_sat input alternating (X := native) (Y := native) _ _

example : (ssaHandledFunctor (model Op) (scripted Op) input).map (graph routeGraph) ≤
    (ssaHandledFunctor (model Op) (scripted Op) input).map (graph echoGraph) ↔
      (rankedRoom Op).Sat ⟨scriptedModel⟩ (rankedOf routeGraph echoGraph) :=
  ssaHandledFunctor_map_le_iff_sat input (scripted Op) (X := written) (Y := written) routeGraph echoGraph

/-- The emitted LetCase sentence of the two graphs is the pair of their
emitted operands. -/
example : ((readCorridor Op ≫ grammarCaseCorridor Op).sen (rankedOf routeGraph echoGraph)) =
    captured routeGraph.toLetCase echoGraph.toLetCase :=
  grammarCase_read_rankedOf routeGraph echoGraph

/-! ## A renaming that keeps the typed interface -/

private inductive Query | probe

private def rename : Query → Op
  | .probe => .ask

private theorem rename_injective : Function.Injective rename := fun a b _ => by cases a; cases b; rfl

/-- The single stage written over the renamed primitive. -/
private def routeQuery : Operand (Pulled rename) Source Packet :=
  ⟨.let₁ (.op Query.probe (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inl .bv) (.inr (.inl .bv)))⟩

private def echoQuery : Operand (Pulled rename) Source Packet :=
  ⟨.let₁ (.op Query.probe (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 1) (.inr (.inl .unit)) (.inl .unit)),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inr (.inl .unit)) (.inl .unit))⟩

/-- Renaming gives the original operands at the same typing index. -/
example : renameCase rename (captured routeQuery echoQuery) = captured route echo := rfl

/-- The satisfaction condition: the renamed sentence holds in a model
exactly when the original holds in the reduct. -/
example (N : HandledModel Op) :
    SatLe N (captured route echo) ↔ SatLe (N.reduct (renameEvents rename)) (captured routeQuery echoQuery) :=
  satLe_rename rename_injective N (captured routeQuery echoQuery)

/-- At the model that admits every reply, the reduct is again that model. -/
example : SatLe allReplies (captured route echo) ↔
    SatLe (allRepliesModel (events (Pulled rename))) (captured routeQuery echoQuery) := by
  rw [← reduct_allReplies rename]
  exact satLe_rename rename_injective allReplies (captured routeQuery echoQuery)

/-- The composites over the renamed primitive rename to the composites. -/
private abbrev compositesQuery : CaseEquation (sig (Pulled rename)) :=
  captured (Case.seq routeQuery routeQuery) (Case.seq routeQuery echoQuery)

example : renameCase rename compositesQuery = composites := rfl

/-- The reduct of the state-flipping model satisfies the renamed-away
sentence in both directions, by the satisfaction condition. -/
example : SatLe (alternatingModel.reduct (renameEvents rename)) compositesQuery ∧
    SatLe (alternatingModel.reduct (renameEvents rename)) (swap compositesQuery) :=
  ⟨(satLe_rename rename_injective alternatingModel compositesQuery).mp alternating_satisfies.1,
    (satLe_rename rename_injective alternatingModel (swap compositesQuery)).mp alternating_satisfies.2⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
