module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.ChainProofs

open CarriedAddress.Institution.RuntimeEntry (Entry)
open Linked.Satisfaction.ReductImage (CaptureChain)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q : EntrySignature} {cells : Nat}

theorem mapChain_eq (sentence : Sentence P) (chain : CaptureChain P Q) :
    sentence.mapChain chain = sentence.map chain.composite := by
  induction chain with
  | nil => exact (Sentence.map_id sentence).symm
  | cons head tail ih => exact (ih (sentence.map head)).trans (sentence.map_comp head tail.composite).symm

theorem satisfaction_liftChain (backend : Backend) (sentence : Sentence P)
    {chain : CaptureChain P Q} {source : Entry P.args cells} {stages : CaptureChain.Stages cells chain}
    (lifted : chain.lift? source = some stages) :
    backend.Holds (sentence.mapChain chain) stages.last.model ↔ backend.Holds sentence source.model := by
  obtain ⟨first, edges, _⟩ := CaptureChain.lift?_sound lifted
  have pulled : reduct chain.composite stages.last.model = source.model :=
    congrArg (Entry.model (P := P)) ((stages.first_eq_reduct_last edges).symm.trans first)
  rw [mapChain_eq, backend.satisfaction_map, pulled]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.ChainProofs
