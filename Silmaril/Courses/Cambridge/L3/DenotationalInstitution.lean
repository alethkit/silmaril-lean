module

public import Silmaril.Courses.Cambridge.L3.Denotation.CallDepth
public import Silmaril.Courses.Cambridge.ReturnSpecification.Institution

/-! # Denotational truth for the L3 finite may-return institution -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.DenotationalInstitution

open Denotation
open ReturnSpecification (Claim)
open Silmaril.Semantics.Operational

/-- A denotational observation retains both the value expression and the store. -/
def observesReturn (source target : Config) : Prop :=
  ∃ v : Value, v.val = target.expr ∧ Returns (denote source.expr) source.store v target.store

private theorem observesReturn_iff_of_adequate (source target : Config) (computation : Computation Value)
    (adequate : ∀ (v : Value) (t : Store), Returns computation source.store v t ↔
      Steps source ⟨v.val, t⟩) :
    (∃ v : Value, v.val = target.expr ∧ Returns computation source.store v target.store) ↔
      OperationalInstitution.semantics.May source (.returned target) := by
  rw [OperationalInstitution.may_return_iff]
  rcases target with ⟨e', t⟩
  constructor
  · rintro ⟨⟨v, ready⟩, rfl, returned⟩
    exact ⟨(adequate ⟨v, ready⟩ t).mp returned, ready⟩
  · rintro ⟨trace, ready⟩
    exact ⟨⟨e', ready⟩, rfl, (adequate ⟨e', ready⟩ t).mpr trace⟩

theorem observesReturn_iff (source target : Config) (admitted : Fragment source.expr) :
    observesReturn source target ↔
      OperationalInstitution.semantics.May source (.returned target) :=
  observesReturn_iff_of_adequate source target _ (fun _ _ => Denotation.adequate admitted)

def Admitted : Claim Config → Prop
  | .mayReturn source | .mayReturnTo source _ => Fragment source.expr

def Denotes : Claim Config → Prop
  | .mayReturn source => ∃ target, observesReturn source target
  | .mayReturnTo source target => observesReturn source target

theorem observed_iff (claim : Claim Config) (admitted : Admitted claim) :
    claim.observed (ReturnSpecification.semantics .l3) ↔ Denotes claim := by
  cases claim with
  | mayReturn source =>
      exact exists_congr (fun target => (observesReturn_iff source target admitted).symm)
  | mayReturnTo source target => exact (observesReturn_iff source target admitted).symm

/-- The existing catalogue institution admits denotational evaluation of
every conjunct whose source is in the compositional fragment. -/
theorem holds_iff {slots : Nat} (catalogue : StepSpecification.Catalogue ⟨.l3, slots⟩)
    (sentence : ReturnSpecification.Sentence ⟨.l3, slots⟩)
    (admitted : ∀ claim ∈ sentence, Admitted (claim.map catalogue)) :
    ReturnSpecification.Holds ⟨.l3, slots⟩ catalogue sentence ↔
      ∀ claim ∈ sentence, Denotes (claim.map catalogue) := by
  rw [ReturnSpecification.holds_iff]
  exact forall₂_congr fun claim mem =>
    ((claim.map catalogue).observed_iff .l3).symm.trans
      (observed_iff (claim.map catalogue) (admitted claim mem))

theorem observed_data_iff {T : Ty} (shape : DataType T) (source : Config)
    (admitted : Fragment source.expr) (result : shape.Result) (store : Store) :
    (Claim.mayReturnTo source ⟨(shape.value result).val, store⟩).observed
        (ReturnSpecification.semantics .l3) ↔
      shape.Observes source.expr source.store result store := by
  change OperationalInstitution.semantics.May source (.returned _) ↔ _
  rw [OperationalInstitution.may_return_iff, adequate_data admitted]
  exact and_iff_left (shape.value result).property

namespace CallDepth

/-- Finite denotational returns at the specified depth and let mode
retain the full returned configuration. -/
def observesReturn (depth : Nat) (mode : Denotation.CallDepth.LetMode) (source target : Config) : Prop :=
  ∃ v : Value, v.val = target.expr ∧
    Returns (Denotation.CallDepth.denote depth source.expr mode) source.store v target.store

theorem observesReturn_iff (depth : Nat) (mode : Denotation.CallDepth.LetMode) (source target : Config)
    (admitted : Denotation.CallDepth.Admitted depth Environment.empty source.store source.expr mode) :
    observesReturn depth mode source target ↔
      OperationalInstitution.semantics.May source (.returned target) :=
  observesReturn_iff_of_adequate source target _ (fun _ _ => Denotation.CallDepth.adequate admitted)

def Admitted (depth : Nat) (mode : Denotation.CallDepth.LetMode) : Claim Config → Prop
  | .mayReturn source | .mayReturnTo source _ =>
      Denotation.CallDepth.Admitted depth Environment.empty source.store source.expr mode

def Denotes (depth : Nat) (mode : Denotation.CallDepth.LetMode) : Claim Config → Prop
  | .mayReturn source => ∃ target, observesReturn depth mode source target
  | .mayReturnTo source target => observesReturn depth mode source target

theorem observed_iff (depth : Nat) (mode : Denotation.CallDepth.LetMode) (claim : Claim Config)
    (admitted : Admitted depth mode claim) :
    claim.observed (ReturnSpecification.semantics .l3) ↔ Denotes depth mode claim := by
  cases claim with
  | mayReturn source =>
      exact exists_congr (fun target => (observesReturn_iff depth mode source target admitted).symm)
  | mayReturnTo source target => exact (observesReturn_iff depth mode source target admitted).symm

/-- The registered L3 return institution agrees with the call-depth
denotation when each source is admitted at the chosen depth and mode. -/
theorem holds_iff {slots : Nat} (depth : Nat) (mode : Denotation.CallDepth.LetMode)
    (catalogue : StepSpecification.Catalogue ⟨.l3, slots⟩)
    (sentence : ReturnSpecification.Sentence ⟨.l3, slots⟩)
    (admitted : ∀ claim ∈ sentence, Admitted depth mode (claim.map catalogue)) :
    ReturnSpecification.Holds ⟨.l3, slots⟩ catalogue sentence ↔
      ∀ claim ∈ sentence, Denotes depth mode (claim.map catalogue) := by
  rw [ReturnSpecification.holds_iff]
  exact forall₂_congr fun claim mem =>
    ((claim.map catalogue).observed_iff .l3).symm.trans
      (observed_iff depth mode (claim.map catalogue) (admitted claim mem))

end CallDepth

end Silmaril.Courses.Cambridge.L3.DenotationalInstitution
