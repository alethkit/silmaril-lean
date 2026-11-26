module

public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Proofs

open CategoryTheory
open Diamond (Val dataPorts)
open RVSDG (Tuple)
open SeaOfNodes.MLIR (Word sourceInputs)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {B : Profile} {S T : Signature}

theorem sourceInputs_encodeInput {Γ : List Width} (input : Tuple (Val Word) (dataPorts (inputSorts Γ))) :
    sourceInputs (encodeInput input) = input := by
  induction Γ with
  | nil => cases input; rfl
  | cons w Γ ih =>
    cases input with
    | cons value rest => exact congrArg (Tuple.cons value) (ih rest)

theorem encodeInput_sourceInputs {Γ : List Width} (input : Env Γ) :
    encodeInput (sourceInputs input) = input := by
  induction input with
  | nil => rfl
  | cons value _ ih => exact congrArg (Env.cons value) ih

theorem model_reduct (f : S ⟶ T) :
    Diamond.Institution.reduct f.left (sourceModel T) = sourceModel S := by
  unfold sourceModel
  rw [← Diamond.Institution.reduct_comp, Over.w f]

theorem translate_map (f : S ⟶ T) (s : SourceSentence B S.left) :
    translate T (s.map f.left) = translate S s := by
  unfold translate
  apply congrArg lowerSentence
  apply Subtype.ext
  change (s.val.map f.left).map T.hom = s.val.map S.hom
  rw [← Loop.Institution.Sentence.map_comp, Over.w f]

theorem lowerProgram_observe
    (g : Loop.Institution.Program concrete (inputSorts B.inputs) (.data B.result))
    (oneLatch : g.carried = [.data B.carried]) (input : Env B.inputs) :
    observe (lowerProgram g oneLatch) input =
      (g.graph.denote CF.model (sourceInputs input)).map encodeResult := by
  rcases g with ⟨carried, entrySigs, headerSigs, g⟩
  cases oneLatch
  exact lower_denotePart g input

theorem translateProgram_observe (S : Signature)
    (g : Loop.Institution.Program S.left (inputSorts B.inputs) (.data B.result))
    (oneLatch : g.carried = [.data B.carried])
    (input : Tuple (Val Word) (dataPorts (inputSorts B.inputs))) :
    observe (translateProgram S g oneLatch) (encodeInput input) =
      (g.graph.denote (sourceModel S) input).map encodeResult := by
  erw [translateProgram, lowerProgram_observe]
  rw [sourceInputs_encodeInput]
  exact congrArg (Part.map encodeResult) (Loop.Institution.denote_mapGraph S.hom CF.model g.graph input)

private theorem encodeResult_injective {w : Width} : Function.Injective (@encodeResult w) :=
  fun _ _ equal => congrArg (fun values : Env [w] => values.get .here) (Outcome.returned.inj equal)

theorem map_encodeResult_eq_iff {w : Width} (a b : Part (Word w)) :
    a.map encodeResult = b.map encodeResult ↔ a = b := by
  constructor
  · intro same
    apply Part.ext
    intro result
    have membership (p : Part (Word w)) : encodeResult result ∈ p.map encodeResult ↔ result ∈ p := by
      refine ⟨?_, Part.mem_map encodeResult⟩
      intro member
      obtain ⟨value, present, equal⟩ := (Part.mem_map_iff encodeResult).mp member
      exact encodeResult_injective equal ▸ present
    rw [← membership a, ← membership b, same]
  · intro same
    rw [same]

private theorem lowerSentence_holds (s : SourceSentence B concrete) :
    (lowerSentence s).Holds ↔ s.val.Holds CF.model := by
  obtain ⟨s, admitted⟩ := s
  cases s with
  | equation e =>
    rcases e with ⟨inputs, out, lhs, rhs⟩
    obtain ⟨sameInputs, sameResult, leftLatch, rightLatch⟩ := admitted
    change inputs = inputSorts B.inputs at sameInputs
    change out = .data B.result at sameResult
    subst inputs
    subst out
    change (∀ input, observe (lowerProgram lhs leftLatch) input =
      observe (lowerProgram rhs rightLatch) input) ↔
      ∀ input, lhs.graph.denote CF.model input = rhs.graph.denote CF.model input
    simp only [lowerProgram_observe]
    constructor
    · intro holds input
      have same := (map_encodeResult_eq_iff _ _).mp (holds (encodeInput input))
      erw [sourceInputs_encodeInput] at same
      exact same
    · intro holds input
      exact (map_encodeResult_eq_iff _ _).mpr (holds (sourceInputs input))
  | terminates g =>
    obtain ⟨sameInputs, sameResult, latch⟩ := admitted
    cases sameInputs
    cases sameResult
    change (∀ input, (observe (lowerProgram g latch) input).Dom) ↔
      ∀ input, (g.graph.denote CF.model input).Dom
    simp only [lowerProgram_observe]
    constructor
    · intro holds input
      have domain : (g.graph.denote CF.model (sourceInputs (encodeInput input))).Dom :=
        holds (encodeInput input)
      simpa only [sourceInputs_encodeInput] using domain
    · intro holds input
      exact holds (sourceInputs input)

theorem satisfaction_induced (S : Signature) (s : SourceSentence B S.left) :
    (translate S s).Holds ↔ s.val.Holds (sourceModel S) :=
  (lowerSentence_holds (s.map S.hom)).trans (s.val.satisfaction S.hom CF.model)

end Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.Proofs
