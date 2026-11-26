module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.IdentityLet.ITree.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Extensions.Thms

/-! # An acyclic witness repaired by contextual identity let -/

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IdentityLetExample

open Silmaril.Isotope.LambdaSSA Region
open Paper.TypeCategory Paper.TypeCategory.ITree.Reflection

private theorem leftStep : Paper.IdentityLet.Step [Output, Input]
    (.let₁ (.let₂ (.pair (.let₁ (.var 0) (.var 0)) (.var 0)) (.var 1)) (.br 0 (.var 0)) : Region Op)
    (.let₁ (.let₂ (.pair (.var 0) (.var 0)) (.var 1)) (.br 0 (.var 0))) [Output] := by
  have hv : Tm.HasType [Output, Input] (.var 0 : Tm Op) Output := .var rfl
  have first : Tm.HasType [Output, Output, Output, Input] (.var 1 : Tm Op) Output := .var rfl
  exact .let₁ (.let₂ (.pair (.remove hv) (.same hv)) (.same first)) (.br rfl (.var rfl))

private theorem occurrence
    (Seed : VCtx (Ty Atom) → Region Op → Region Op → LCtx (Ty Atom) → Prop)
    (incl : ∀ {Γ r s L}, Paper.IdentityLet.Step Γ r s L → Seed Γ r s L) :
    Paper.Extension.Eqv Seed [Input] nestedPair plainPair [Output] := by
  obtain ⟨left, right⟩ := leftStep.valueBranches
  have poll : ValueBranches [payload, Input] pollRegion [Output] := .let₁ (.op (.var rfl)) (.br rfl (.var rfl))
  exact .case (.var rfl) (.extra left.hasType right.hasType (incl leftStep)) (.refl poll.hasType)

private theorem pair_projection :
    Paper.IdentityLet.projection.map nestedPairArrow = Paper.IdentityLet.projection.map plainPairArrow :=
  (Paper.Extension.Singleton.ofRegion_eq_iff _ nestedPair_typed plainPair_typed).2 (occurrence _ id)

-- The earlier kernel equation is derived even when the case-return quotient
-- is included. The right branch retains its visible poll.
example : Paper.Extension.Eqv
    (fun Γ r s L => Paper.WithCaseReturns.JoinedStep false Γ r s L ∨ Paper.IdentityLet.Step Γ r s L)
    [Input] nestedPair plainPair [Output] :=
  occurrence _ Or.inr

example : interpretation.map nestedPairArrow = interpretation.map plainPairArrow :=
  Paper.IdentityLet.weakITree_image_eq_of_projection_eq raw compatible _ _ pair_projection

-- The same law applies when the removed binder actually receives a primitive reply.
private theorem poll_typed : Tm.HasType [payload] (.op Op.poll (.var 0) : Tm Op) Output :=
  .op (.var rfl)

private theorem query_typed : Tm.HasType [payload] (.op Op.query (.var 0) : Tm Op) Output :=
  .op (.var rfl)

private theorem effectfulStep :
    Paper.IdentityLet.Step [payload]
      (.let₁ (.pair (.let₁ (.op Op.poll (.var 0)) (.var 0)) (.op Op.query (.var 0))) (.br 0 (.var 0)))
      (.let₁ (.pair (.op Op.poll (.var 0)) (.op Op.query (.var 0))) (.br 0 (.var 0)))
      [Silmaril.product Output Output] :=
  .let₁ (.pair (.remove poll_typed) (.same query_typed)) (.br rfl (.var rfl))

example :
    let hg := effectfulStep.valueBranches
    interpretation.map (ofRegion hg.1) = interpretation.map (ofRegion hg.2) := by
  intro hg
  apply Paper.IdentityLet.weakITree_image_eq_of_projection_eq raw compatible
  exact (Paper.Extension.Singleton.ofRegion_eq_iff _ hg.1 hg.2).2
    (.extra hg.1.hasType hg.2.hasType effectfulStep)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IdentityLetExample
