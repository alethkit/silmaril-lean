module

import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution

open CategoryTheory
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)

private def i8 : Width := ⟨8, by decide⟩
private abbrev word : Diamond.ValueSort Width := .data i8
private abbrev wordPort : Diamond.Ty Width := .value word
private abbrev predPort : Diamond.Ty Width := .value .predicate
private def boundary : Profile := ⟨[], i8, i8⟩

private inductive Primitive : Diamond.Signature.{0, 0} Width where
  | zero : Primitive [] word
  | zeroAlias : Primitive [] word
  | one : Primitive [] word
  | less : Primitive [word, word] .predicate

private abbrev localSig : Diamond.Institution.Signature.{0, 0} Width := ⟨Primitive⟩

private def realization : localSig ⟶ concrete :=
  ⟨fun
    | .zero | .zeroAlias => .arithmetic (.constant (0 : Word i8))
    | .one => .arithmetic (.constant (1 : Word i8))
    | .less => .ult i8⟩

private def realized : Signature := Over.mk realization

private def swapZero : localSig ⟶ localSig :=
  ⟨fun
    | .zero => .zeroAlias
    | .zeroAlias => .zero
    | .one => .one
    | .less => .less⟩

private def rename : realized ⟶ realized := Over.homMk swapZero (by
  change Diamond.Institution.Signature.Hom.mk (P := localSig) (Q := concrete)
      (fun op => realization.opcode (swapZero.opcode op)) =
    Diamond.Institution.Signature.Hom.mk (fun op => realization.opcode op)
  congr 1
  funext _ _ op
  cases op <;> rfl)

private theorem renameNonidentity : swapZero ≠ 𝟙 localSig := by
  intro equal
  have op := congrArg (fun h : localSig ⟶ localSig => h.opcode Primitive.zero) equal
  change Primitive.zeroAlias = Primitive.zero at op
  cases op

-- Initialize the latch to zero. Comparing zero with one takes the self-edge,
-- while comparing one with zero immediately returns the selected wire.
private def loop (continues returnOne : Bool) : Loop.Institution.Program realized.left [] word where
  carried := [word]
  entrySigs := [[wordPort]]
  headerSigs := [[wordPort], [predPort]]
  graph :=
    { preheader := .cons .zero .nil .nil
      header := .cons .one .nil (.cons .less
        (if continues then .cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)
          else .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil)) .nil)
      phiInputs
        | .entry => .cons (.output (0 : Fin 1) .head) .nil
        | .backedge => .cons (.arg .head) .nil
      predicate := .output (1 : Fin 2) .head
      result := if returnOne then .output (0 : Fin 2) .head else .arg .head }

private def compiled (continues returnOne : Bool) : TargetProgram boundary :=
  translateProgram realized (loop continues returnOne) rfl

private theorem exitReturns :
    observe (compiled false true) .nil = Part.some (encodeResult (1 : Word i8)) :=
  (Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart_eq_some_iff _ _ _ _).mpr ⟨3, rfl⟩

private theorem noSourceReturn (returnOne : Bool) (result : Word i8) :
    ¬ (loop true returnOne).graph.Returns (sourceModel realized) .nil result :=
  (loop true returnOne).graph.not_returns_of_backedge_invariant (sourceModel realized) .nil result
    (· = .cons (0 : Word i8) .nil) rfl
    (fun _old same => same.symm ▸ ⟨.cons (0 : Word i8) .nil, rfl, rfl⟩)

private theorem spinUndefined (returnOne : Bool) :
    observe (compiled true returnOne) .nil = Part.none :=
  (observe_none_iff (B := boundary) realized (loop true returnOne) rfl .nil).mpr
    (Part.eq_none_iff.mpr fun result member =>
      noSourceReturn returnOne result
        (((loop true returnOne).graph.returns_iff_mem_denote (sourceModel realized) .nil result).mpr member))

private def equation (continues : Bool) : SourceSentence boundary realized.left :=
  ⟨.equation ⟨[], word, loop continues true, loop true false⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

private theorem divergentEquation :
    (translate realized (equation true)).Holds := by
  intro input
  cases input
  change observe (compiled true true) .nil = observe (compiled true false) .nil
  exact (spinUndefined true).trans (spinUndefined false).symm

private theorem mixedEquationFails :
    ¬ (translate realized (equation false)).Holds := by
  intro holds
  have same := holds .nil
  change observe (compiled false true) .nil = observe (compiled true false) .nil at same
  rw [exitReturns, spinUndefined false] at same
  exact Part.some_ne_none _ same

private theorem reflectsDivergentEquation :
    (equation true).val.Holds (sourceModel realized) :=
  (satisfaction_induced realized (equation true)).mp divergentEquation

private theorem renamedDivergentEquation :
    (translate realized ((equation true).map rename.left)).Holds := by
  rw [translate_map rename]
  exact divergentEquation

private def termination (continues : Bool) : SourceSentence boundary realized.left :=
  ⟨.terminates (loop continues true), ⟨rfl, rfl, rfl⟩⟩

private theorem exitingTerminates : (translate realized (termination false)).Holds := by
  intro input
  cases input
  change (observe (compiled false true) .nil).Dom
  rw [exitReturns]
  exact Part.some_dom _

private theorem spinningDoesNotTerminate : ¬ (translate realized (termination true)).Holds := by
  intro holds
  have defined := holds .nil
  change (observe (compiled true true) .nil).Dom at defined
  rw [spinUndefined true] at defined
  exact Part.not_none_dom defined

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution
