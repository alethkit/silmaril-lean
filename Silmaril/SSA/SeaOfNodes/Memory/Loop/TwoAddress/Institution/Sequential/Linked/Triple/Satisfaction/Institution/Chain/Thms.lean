module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Chain

/-! Satisfaction along checked capture chains in the generated institutions. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Linked.Satisfaction (InReductImage)
open Linked.Satisfaction.ReductImage (CaptureChain)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q R : EntrySignature} {cells : Nat}

theorem Sentence.mapChain_eq (sentence : Sentence P) (chain : CaptureChain P Q) :
    sentence.mapChain chain = sentence.map chain.composite :=
  ChainProofs.mapChain_eq sentence chain

theorem Sentence.mapChain_append (sentence : Sentence P) (left : CaptureChain P Q) (right : CaptureChain Q R) :
    sentence.mapChain (left.append right) = (sentence.mapChain left).mapChain right := by
  simp only [Sentence.mapChain_eq, CaptureChain.composite_append, Sentence.map_comp]

/-- At the checked final valuation, staged re-emission has the source
sentence's truth in the numbered, MemRef or coloured room. -/
theorem Backend.satisfaction_liftChain (backend : Backend) (sentence : Sentence P)
    {chain : CaptureChain P Q} {source : Entry P.args cells} {stages : CaptureChain.Stages cells chain}
    (lifted : chain.lift? source = some stages) :
    backend.Holds (sentence.mapChain chain) stages.last.model ↔ backend.Holds sentence source.model :=
  ChainProofs.satisfaction_liftChain backend sentence lifted

/-- All-target truth at this cell count tests source valuations in the
typed image of the composite reduct. -/
theorem Sentence.room_satisfaction_chain_image (sentence : Sentence P) (backend : Backend)
    (chain : CaptureChain P Q) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (sentence.mapChain chain).numbered ↔
      ∀ input : Tuple (Val cells) P.args, InReductImage chain.composite input →
        backend.Holds sentence ⟨cells, input⟩ := by
  rw [sentence.mapChain_eq, sentence.room_satisfaction_image]

/-- A successful terminal coverage check allows quantification over every
source valuation at this cell count. -/
theorem Sentence.room_satisfaction_chain_of_check (sentence : Sentence P) (backend : Backend)
    (chain : CaptureChain P Q) (cells : Nat) (covered : chain.checkCoverage cells = true) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (sentence.mapChain chain).numbered ↔
      ∀ input : Tuple (Val cells) P.args, backend.Holds sentence ⟨cells, input⟩ := by
  rw [sentence.room_satisfaction_chain_image backend chain cells]
  exact ⟨fun holds input => holds input ((Linked.Satisfaction.ReductImage.checkCoverage_iff chain.composite cells).mp
    covered input), fun holds input _ => holds input⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction
