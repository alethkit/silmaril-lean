module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Selected.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected

open CategoryTheory
open LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement (ReadTree)
open Silmaril.Semantics.NondeterministicTrace (Tagged)

set_option backward.isDefEq.respectTransparency false

theorem denotation_eq_iff_normal_proof (H : Sorts) (L : List Sorts) (p q : ReadTree (H :: L) 0) :
    denotation p = denotation q ↔ (witnessed p).normal Fin.elim0 = (witnessed q).normal Fin.elim0 := by
  have outcomes (t : ReadTree (H :: L) 0) :
      ((denotation t).of PUnit.unit).outcomes = Extensional.programOutcomes H L (witnessed t) Fin.elim0 :=
    t.packedOutcomes_eq H L
  have arrow_iff : denotation p = denotation q ↔
      ((denotation p).of PUnit.unit).outcomes = ((denotation q).of PUnit.unit).outcomes := by
    constructor
    · intro equal
      rw [equal]
    · intro equal
      apply CategoryTheory.Kleisli.hom_ext
      apply ConcreteCategory.coe_ext
      funext x
      cases x
      exact Tagged.outcomes_injective equal
  exact arrow_iff.trans (by
    rw [outcomes p, outcomes q]
    exact Extensional.programOutcomes_iff_normal H L (witnessed p) (witnessed q) Fin.elim0)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional.Selected
