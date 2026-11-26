module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement

/-! # The intrinsic and witnessed observations of the same payload request -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

open Silmaril CategoryTheory
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply (Trace)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit signature model modelCoherent)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open Silmaril.Isotope.LetIter.Semantics.Categorical (boundEnv)
open Paper.WithProjectionReturnsAndUnitEta (denoteArrow)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The packed selected tree and the witnessed LetCase program have the same
set of tagged outcomes. Both use the published payload separator's algebra and
the source program's emit prefixes, bound replies and ordered exit positions. -/
theorem DirectProgram.packedOutcomes_eq (H : Ty Empty) (L : List (Ty Empty)) (p : DirectProgram (H :: L)) :
    letI := Kleisli.instructions model
    let := modelCoherent
    ((denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit).outcomes =
      Reply.Payload.programOutcomes H L p.val :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement.packed_outcomes H L p

/-- The packed intrinsic arrow at unit gives the concrete computation of
the separator's actual witnessed LetCase program in the closed environment. -/
theorem DirectProgram.denote_agrees (H : Ty Empty) (L : List (Ty Empty)) (p : DirectProgram (H :: L)) :
    letI := Kleisli.instructions model
    let := modelCoherent
    (denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit =
      Kleisli.run model (Reply.Payload.program H L p.val).toLetCase.2
        (boundEnv Kleisli.value (β := .nil) PUnit.unit) :=
  Tagged.outcomes_injective (p.packedOutcomes_eq H L)

/-- The selected fold and the actual witnessed finite tree have equal
packed observations. Each return may read any live reply slot. -/
theorem ReadTree.packedOutcomes_eq (H : Ty Empty) (L : List (Ty Empty)) (p : ReadTree (H :: L) 0) :
    letI := Kleisli.instructions model
    let := modelCoherent
    ((denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit).outcomes =
      Reply.Payload.Finite.programOutcomes H L p.witnessed :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement.readTree_packed_outcomes H L p

/-- In the validated separator model the packed intrinsic computation
equals evaluation of the same finite witnessed LetCase tree. -/
theorem ReadTree.denote_agrees (H : Ty Empty) (L : List (Ty Empty)) (p : ReadTree (H :: L) 0) :
    letI := Kleisli.instructions model
    let := modelCoherent
    (denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit =
      Kleisli.run model (Reply.Payload.Finite.program H L p.witnessed).toLetCase.2
        (boundEnv Kleisli.value (β := .nil) PUnit.unit) :=
  Tagged.outcomes_injective (p.packedOutcomes_eq H L)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement
