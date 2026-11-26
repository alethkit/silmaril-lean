module

public import Silmaril.Machine.MulticoreVM.Placed.Institution.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Thms
public import Silmaril.Machine.MulticoreVM.Institution.Thms
public import Silmaril.Semantics.ConcurrentTrace.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Placed.Institution

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Placed

open CategoryTheory
open Institution (Sig)
open Silmaril.Semantics.ConcurrentTrace (ofWord mapTrace_ofWord)

universe u

variable {A B : Sig.{u}}

/-- Forgetting core tags commutes with the observation maps of a typed signature morphism. -/
theorem forgetInstitutionCore_mapCore (f : A ⟶ B) (word : A.CoreWord) :
    forgetInstitutionCore (Sig.Hom.mapCore f word) =
      Sig.Hom.mapNamed f (forgetInstitutionCore word) :=
  Proofs.Machine.MulticoreVM.Placed.forgetInstitutionCore_mapCore f word

theorem forgetInstitutionCore_toInstitutionCoreWord
    (word : TaggedWord A.CoreId A.ThreadId A.Event) :
    forgetInstitutionCore (toInstitutionCoreWord word) = threadWord word :=
  Proofs.Machine.MulticoreVM.Placed.forgetInstitutionCore_toInstitutionCoreWord word

theorem toInstitutionCoreWord_mapTaggedWord (f : A ⟶ B)
    (word : TaggedWord A.CoreId A.ThreadId A.Event) :
    toInstitutionCoreWord (mapTaggedWord f.core f.thread f.event word) =
      Sig.Hom.mapCore f (toInstitutionCoreWord word) :=
  Proofs.Machine.MulticoreVM.Placed.toInstitutionCoreWord_mapTaggedWord f word

/-- The projection from core-tagged to thread-named institution observations. -/
def institutionForgetCore : Institution.coreWords.{u} ⟶ Institution.namedWords.{u} where
  app _ := TypeCat.ofHom forgetInstitutionCore
  naturality _ _ f := TypeCat.homEquiv.injective (funext (forgetInstitutionCore_mapCore f))

/-- The quotient from thread-named words to concurrent institution observations. -/
def institutionNamedQuotient : Institution.namedWords.{u} ⟶ Institution.concurrentTraces.{u} where
  app _ := TypeCat.ofHom ofWord
  naturality _ _ f := TypeCat.homEquiv.injective
    (funext fun word => (mapTrace_ofWord f.thread f.thread.injective f.event word).symm)

/-- The institution's two projections recover the concurrent thread observation of a C8 word. -/
theorem threadTrace_eq_institution (word : TaggedWord A.CoreId A.ThreadId A.Event) :
    (institutionForgetCore ≫ institutionNamedQuotient).app A (toInstitutionCoreWord word) =
      threadTrace word := by
  change ofWord (forgetInstitutionCore (toInstitutionCoreWord word)) = threadTrace word
  rw [forgetInstitutionCore_toInstitutionCoreWord, threadTrace]

section Behavior

variable {Core Thread Choice : Type u} [DecidableEq A.CoreId]
variable {instruction : Instruction A.CoreId A.ThreadId Core Thread Choice A.Event}
variable {step : Transition (A.ThreadId → Option Thread) A.ThreadId Choice A.Event}

/-- After hiding the final store, named concrete observations are admitted by the institution's
abstract VM model. -/
theorem threadWord_image_subset_namedModel (refines : instruction.Refines step)
    (schedule : Schedule A.CoreId A.ThreadId Choice) (initial : Config A.CoreId A.ThreadId Core Thread) :
    (threadWord ∘ Prod.snd) '' taggedOutcomes instruction schedule initial ⊆
      Institution.namedModel (A := A) step initial.threads := by
  rintro _ ⟨outcome, concrete, rfl⟩
  exact ⟨threadSchedule schedule, threadWord outcome.2, outcome.1.threads,
    Scheduled.refines refines concrete, rfl⟩

/-- After hiding the final store, quotient concrete observations are admitted by the institution's
abstract concurrent VM model. -/
theorem threadTrace_image_subset_concurrentModel (refines : instruction.Refines step)
    (schedule : Schedule A.CoreId A.ThreadId Choice) (initial : Config A.CoreId A.ThreadId Core Thread) :
    (threadTrace ∘ Prod.snd) '' taggedOutcomes instruction schedule initial ⊆
      Institution.concurrentModel (A := A) step initial.threads := by
  rintro _ ⟨outcome, concrete, rfl⟩
  exact ⟨threadSchedule schedule, threadWord outcome.2, outcome.1.threads,
    Scheduled.refines refines concrete, rfl⟩

end Behavior

end Silmaril.Machine.MulticoreVM.Placed
