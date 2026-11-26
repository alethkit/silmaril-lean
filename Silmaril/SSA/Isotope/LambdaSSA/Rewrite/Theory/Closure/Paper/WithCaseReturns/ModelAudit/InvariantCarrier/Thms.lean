module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.ModelAudit.InvariantCarrier.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier

/-! # The nonterminating-state subtype need not be a syntax type -/

public section

open CategoryTheory
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.ModelAudit.InvariantCarrier

attribute [local instance] typeModel categoricalInstructions

/-- Exactly the payloads outside the singleton sets have finite return traces. -/
theorem returns_iff (x : Atom) : Returns x ↔ ¬ IsSingleton x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier.returns_iff x

/-- Every syntax carrier is finite or contains a copy of the full atom.
The countably infinite nonterminating-state subtype has neither size. -/
theorem no_invariant_carrier (t : Ty AtomSort) :
    ¬ Nonempty (Ty.denote carrier t ≃ {x : Atom // ¬ Returns x}) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier.no_invariant_carrier t

/-- There is no injective input map from a syntax carrier whose image is
exactly the nonterminating-state subtype. -/
theorem no_exact_inclusion (t : Ty AtomSort) (f : Ty.denote carrier t → Atom)
    (injective : Function.Injective f)
    (image : ∀ x, (∃ a, f a = x) ↔ ¬ Returns x) : False :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier.no_exact_inclusion t f injective image

/-- The actual guarded singleton denotation returns the tagged step in
the typed observation model. -/
theorem step_observation (x : Atom) :
    (show TreeM (PUnit.{2} ⊕ Atom) from
      (denoteSingletonRegion computation typeInterpretation body_typed.hasType).of x) = pure (next x) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier.step_observation x

/-- The interpretation validates the whole old case-return relation on
this instruction signature, including its contextual rules. -/
theorem quotient_observation_sound {Γ : VCtx (Ty AtomSort)} {L : LCtx (Ty AtomSort)} {r s : Region Op}
    (eq : Paper.WithCaseReturns.Eqv false Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion computation typeInterpretation hr = denoteRegion computation typeInterpretation hs :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier.quotient_observation_sound eq hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.ModelAudit.InvariantCarrier
