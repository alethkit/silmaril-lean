module

public import Silmaril.Courses.Cambridge.L2ToL3.Thms
public import Silmaril.Courses.Cambridge.ReturnSpecification.Institution

/-! Finite may-return sentences transport from typed L2 sources to the
existing L3 observer by embedding complete configurations. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2ToL3.ReturnInstitution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Fragments
open ReturnSpecification
open StepSpecification (Context Catalogue)

def source : Claim L2.Config → L2.Config
  | .mayReturn c | .mayReturnTo c _ => c

/-- Only the start of a claim needs a typing derivation. A proposed
destination can name any L2 configuration, including a wrong final store. -/
def SourceTyped (claim : Claim L2.Config) : Prop :=
  ∃ Γ T, L2.HasType Γ (source claim).expr T

abbrev TypedClaim := {claim : Claim L2.Config // SourceTyped claim}

theorem observed_iff (address : Layout) (claim : Claim L2.Config) (typed : SourceTyped claim) :
    (claim.map (config address)).observed (semantics .l3) ↔
      claim.observed (semantics .l2) := by
  obtain ⟨Γ, T, ht⟩ := typed
  cases claim with
  | mayReturn start =>
      constructor
      · rintro ⟨target, observed⟩
        obtain ⟨result, returned, _⟩ := reflect_may_return address ht observed
        exact ⟨result, returned⟩
      · rintro ⟨target, observed⟩
        exact ⟨config address target, may_return address observed⟩
  | mayReturnTo start target => exact may_return_iff address ht

abbrev typedSignature : AtomicSignature := ⟨TypedClaim⟩
abbrev typedRoom := observationLogic.obj typedSignature
abbrev targetRoom := observationLogic.obj (signature L3.Config)

/-- Restrict the existing L2 observer to the admitted claims. -/
def sourceModel : typedRoom.Mod :=
  (observationLogic.map ⟨Subtype.val⟩).mod.obj (observationModel .l2)

/-- Translate the existing claim constructors on full configurations and
extend the translation to conjunctions using the existing return logic. -/
def translation (address : Layout) : typedRoom ⟶ targetRoom :=
  observationLogic.map ⟨fun claim : TypedClaim => claim.val.map (config address)⟩

/-- Reducing the registered L3 observer gives exactly the typed L2 observer. -/
theorem reduct (address : Layout) :
    (translation address).mod.obj (observationModel .l3) = sourceModel := by
  exact congrArg Discrete.mk (funext fun claim : TypedClaim =>
    propext (observed_iff address claim.val claim.property))

theorem satisfaction (address : Layout) (sentence : List TypedClaim) :
    targetRoom.Sat (observationModel .l3) ((translation address).sen sentence) ↔
      typedRoom.Sat sourceModel sentence := by
  have sat := (translation address).sat (observationModel .l3) sentence
  rw [reduct address] at sat
  exact sat

/-- For named documents the slot numbers stay fixed and their catalogue
entries move to L3. Only the source slots used by the sentence need typing. -/
theorem holds_iff (address : Layout) {n : Nat} (catalogue : Catalogue ⟨.l2, n⟩)
    (sentence : Sentence ⟨.l2, n⟩)
    (typed : ∀ claim ∈ sentence, SourceTyped (claim.map catalogue)) :
    Holds ⟨.l3, n⟩ (config address ∘ catalogue) sentence ↔ Holds ⟨.l2, n⟩ catalogue sentence := by
  change (∀ claim ∈ sentence, (claim.map (config address ∘ catalogue)).observed (semantics .l3)) ↔
    (∀ claim ∈ sentence, (claim.map catalogue).observed (semantics .l2))
  apply forall₂_congr
  intro claim member
  have equal : claim.map (config address ∘ catalogue) = (claim.map catalogue).map (config address) := by
    cases claim <;> rfl
  rw [equal]
  exact observed_iff address _ (typed claim member)

end Silmaril.Courses.Cambridge.L2ToL3.ReturnInstitution
