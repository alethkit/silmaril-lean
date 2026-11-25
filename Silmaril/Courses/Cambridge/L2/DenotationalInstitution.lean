module

public import Silmaril.Courses.Cambridge.L2.Denotation.Relational.Institution
public import Silmaril.Courses.Cambridge.ReturnSpecification.Institution

/-! # Denotational truth for the L2 CBV return catalogue -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.DenotationalInstitution

open ReturnSpecification (Claim)
open Silmaril.Semantics.Operational

/-- A return observes the quoted value and the full final store. The catalogue
supplies configurations interpreted with the empty lexical environment. -/
def observesReturn (source target : Config) : Prop :=
  RelationalDenotation.Observes [] source.expr source.store target

theorem observesReturn_iff (source target : Config) :
    observesReturn source target ↔
      (ReturnSpecification.semantics .l2).May source (.returned target) :=
  RelationalDenotation.sat_iff source target

/-- The existential witness ranges over all configurations. -/
def Denotes : Claim Config → Prop
  | .mayReturn source => ∃ target, observesReturn source target
  | .mayReturnTo source target => observesReturn source target

theorem observed_iff (claim : Claim Config) :
    claim.observed (ReturnSpecification.semantics .l2) ↔ Denotes claim := by
  cases claim with
  | mayReturn source =>
      exact exists_congr (fun target => (observesReturn_iff source target).symm)
  | mayReturnTo source target => exact (observesReturn_iff source target).symm

/-- Every sentence in the registered L2 catalogue is true exactly when its
translated claims hold in the CBV relational denotation. -/
theorem holds_iff {slots : Nat} (catalogue : StepSpecification.Catalogue ⟨.l2, slots⟩)
    (sentence : ReturnSpecification.Sentence ⟨.l2, slots⟩) :
    ReturnSpecification.Holds ⟨.l2, slots⟩ catalogue sentence ↔
      ∀ claim ∈ sentence, Denotes (claim.map catalogue) := by
  rw [ReturnSpecification.holds_iff]
  exact forall₂_congr fun claim _ =>
    ((claim.map catalogue).observed_iff .l2).symm.trans (observed_iff (claim.map catalogue))

end Silmaril.Courses.Cambridge.L2.DenotationalInstitution
