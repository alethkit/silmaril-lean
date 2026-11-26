module

import Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution

open CategoryTheory
open Diamond (Ty Val ValueSort dataPorts)
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution.RuntimeObservation (observe)

private abbrev word : ValueSort Unit := .data ()
private abbrev wordPort : Ty Unit := .value word
private abbrev predicatePort : Ty Unit := .value .predicate

private inductive Primitive : Diamond.Signature.{0, 0} Unit where
  | nonzero : Primitive [word] .predicate
  | reset : Primitive [word] word
  | keep : Primitive [word] word

private abbrev sig : Diamond.Institution.Signature.{0, 0} Unit := ⟨Primitive⟩

private def arithmetic : Diamond.Model.{0, 0, 0} sig.op where
  value _ := Nat
  run
    | .nonzero, .cons n .nil => ⟨(show Nat from n) != 0⟩
    | .reset, .cons _ .nil => (0 : Nat)
    | .keep, .cons n .nil => n

private def stopResetting : sig ⟶ sig :=
  ⟨fun
    | .nonzero => .nonzero
    | .reset => .keep
    | .keep => .keep⟩

private def loop (update : Primitive [word] word) : Loop.Institution.Program sig [word] word where
  carried := [word]
  entrySigs := []
  headerSigs := [[predicatePort], [wordPort]]
  graph :=
    { preheader := .nil
      header :=
        .cons .nonzero (.cons (.arg (.tail .head)) .nil)
          (.cons update (.cons (.arg (.tail .head)) .nil) .nil)
      phiInputs
        | .entry => .cons (.arg .head) .nil
        | .backedge => .cons (.output (1 : Fin 2) .head) .nil
      predicate := .output (0 : Fin 2) .head
      result := .output (1 : Fin 2) .head }

private def entry (n : Nat) : Tuple (Val arithmetic.value) (dataPorts [word]) :=
  .cons n .nil

private theorem returnsZero :
    observe (thetaRuntime arithmetic) (loop .reset).graph.lowerTheta (entry 4) = Part.some (entry 0) :=
  ((loop .reset).graph.lowerTheta_observe_eq_some arithmetic (entry 4) (0 : Nat)).mp
    ⟨1, .backedge (next := entry 0) (by cbv) (.exit (by cbv))⟩

-- The relabelled update preserves the nonzero latch, so every test continues.
private theorem neverReturns (result : Nat) :
    ¬ (loop .keep).graph.Returns arithmetic (entry 4) result :=
  (loop .keep).graph.not_returns_of_backedge_invariant arithmetic (entry 4) result
    (· = entry 4) rfl (fun old same => same.symm ▸ ⟨entry 4, by cbv, rfl⟩)

private theorem keepingDiverges :
    observe (thetaRuntime arithmetic) (loop .keep).graph.lowerTheta (entry 4) = Part.none := by
  apply Part.eq_none_iff.mpr
  intro output observed
  cases output with
  | cons result tail =>
    cases tail
    exact neverReturns result (((loop .keep).graph.lowerTheta_observe_eq_some arithmetic (entry 4) result).mpr
      (Part.eq_some_iff.mpr observed))

private theorem relabelledThetaDiverges :
    observe (thetaRuntime arithmetic)
      (RVSDG.NestedTheta.Institution.mapGraph (opcodeMap stopResetting) (loop .reset).graph.lowerTheta)
        (entry 4) = Part.none := by
  rw [← lowerTheta_map stopResetting (loop .reset).graph]
  exact keepingDiverges

private def termination : Loop.Institution.Sentence sig := .terminates (loop .reset)

private theorem terminatesInTheta : (translate termination).Holds (thetaRuntime arithmetic) := by
  apply (satisfaction_induced termination arithmetic).mpr
  apply (Loop.Institution.terminates_holds_iff_returns (loop .reset) arithmetic).mpr
  intro input
  cases input with
  | cons n tail =>
    cases tail
    cases n with
    | zero => exact ⟨(0 : Nat), 0, .exit (by cbv)⟩
    | succ n => exact ⟨(0 : Nat), 1, .backedge (next := entry 0) (by cbv) (.exit (by cbv))⟩

private theorem relabelledTerminationFails :
    ¬ ((translate termination).map (signatureMap stopResetting)).Holds (thetaRuntime arithmetic) := by
  intro holds
  have defined := holds (entry 4)
  change (observe (thetaRuntime arithmetic)
    (RVSDG.NestedTheta.Institution.mapGraph (opcodeMap stopResetting) (loop .reset).graph.lowerTheta)
      (entry 4)).Dom at defined
  rw [relabelledThetaDiverges] at defined
  exact Part.not_none_dom defined

private def equation : Loop.Institution.Sentence sig :=
  .equation ⟨[word], word, loop .reset, loop .keep⟩

private theorem equationFails : ¬ (translate equation).Holds (thetaRuntime arithmetic) := by
  intro holds
  have same := holds (entry 4)
  change observe (thetaRuntime arithmetic) (loop .reset).graph.lowerTheta (entry 4) =
    observe (thetaRuntime arithmetic) (loop .keep).graph.lowerTheta (entry 4) at same
  rw [returnsZero, keepingDiverges] at same
  exact Part.some_ne_none _ same

private theorem relabelledEquationHolds :
    ((translate equation).map (signatureMap stopResetting)).Holds (thetaRuntime arithmetic) := by
  rw [← translate_map]
  intro input
  rfl

end Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution
