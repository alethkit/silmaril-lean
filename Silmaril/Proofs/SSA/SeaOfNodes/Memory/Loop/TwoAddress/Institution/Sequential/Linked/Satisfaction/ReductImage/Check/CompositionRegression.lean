module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory
open RVSDG (Tuple)
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature
open Triple.Satisfaction (Backend)
open Triple.Satisfaction renaming Program → TripleProgram, Sentence → TripleSentence
open Sequential.Fixture (captures graph initial)
open Linked.Fixture (combined first wiring inputs rightStore)
open Triple.Fixture (thirdWiring)

private abbrev extended : EntrySignature := ⟨.word :: combined.args⟩
private def insert : combined ⟶ extended := ⟨fun port => .tail port⟩

-- The second map identifies the spare source slot with the right store slot.
private def identifySpare : extended ⟶ extended :=
  ⟨fun
    | .head => .tail rightStore
    | .tail port => .tail port⟩

private def source : Entry combined.args 6 := ⟨inputs, initial⟩
private def greedy : Tuple (Val 6) extended.args := .cons (0 : Word) inputs
private def intermediate : Entry extended.args 6 := ⟨.cons (22 : Word) inputs, initial⟩
private def target : Entry extended.args 6 := ⟨greedy, initial⟩

example : liftInput? insert source.input = some greedy := rfl
example : liftInput? identifySpare greedy = none := rfl

example : (liftInput? insert source.input >>= liftInput? identifySpare) = none := rfl

example : liftInput? (insert ≫ identifySpare) source.input = some target.input := rfl

private theorem recovered : liftThrough? insert identifySpare source = some (intermediate, target) := rfl

example : intermediate.reduct insert = source ∧ target.reduct identifySpare = intermediate :=
  liftThrough?_sound insert identifySpare recovered

-- The recovered intermediate is itself accepted by the second checker.
example : liftInput? identifySpare intermediate.input = some target.input := rfl

example : ¬ InReductImage identifySpare greedy :=
  fun image => (by decide : (liftInput? identifySpare greedy).isSome ≠ true)
    ((liftInput?_isSome_iff identifySpare greedy).mpr image)

example : InReductImage (insert ≫ identifySpare) source.input :=
  (inReductImage_comp_iff_lift insert identifySpare source.input).mpr ⟨intermediate.input, rfl, rfl⟩

example (backend : Backend) (sentence : TripleSentence combined) :
    backend.Holds ((sentence.map insert).map identifySpare) target.model ↔ backend.Holds sentence source.model :=
  backend.satisfaction_liftThrough insert identifySpare sentence recovered

private def original : TripleProgram combined := ⟨⟨captures, first, graph, wiring⟩, captures, graph, thirdWiring⟩

private def runWithLift (p : TripleProgram extended) : Option (Word × Word × Word × List Word) := do
  let (_, target) ← liftThrough? insert identifySpare source
  let (firstWord, secondWord, thirdWord, buffer) ← p.runMemRef target.model 11 ⟨target.heap⟩
  pure (firstWord, secondWord, thirdWord, (List.finRange 6).map buffer.cell)

#guard runWithLift ((original.map insert).map identifySpare) == some (3, 3, 22, [11, 73, 11, 3, 91, 22])
#guard runWithLift (original.map (insert ≫ identifySpare)) == some (3, 3, 22, [11, 73, 11, 3, 91, 22])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
