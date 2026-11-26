module

public import Silmaril.Machine.MulticoreVM.Placed.Institution.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Placed

open CategoryTheory
open Silmaril.Machine.MulticoreVM.Institution (Sig)
open Silmaril.Machine.MulticoreVM.Placed (TaggedWord forgetInstitutionCore mapTaggedWord
  toInstitutionCoreWord threadWord)
open Silmaril.Semantics.ConcurrentTrace (mapWord)

universe u

variable {A B : Sig.{u}}

theorem forgetInstitutionCore_mapCore (f : A ⟶ B) (word : A.CoreWord) :
    forgetInstitutionCore (Sig.Hom.mapCore f word) =
      Sig.Hom.mapNamed f (forgetInstitutionCore word) := by
  simp only [forgetInstitutionCore, Sig.Hom.mapCore, Sig.Hom.mapNamed, mapWord, List.map_map]
  apply List.map_congr_left
  intro tagged _
  cases tagged
  rfl

theorem forgetInstitutionCore_toInstitutionCoreWord
    (word : TaggedWord A.CoreId A.ThreadId A.Event) :
    forgetInstitutionCore (toInstitutionCoreWord word) = threadWord word := by
  simp only [forgetInstitutionCore, toInstitutionCoreWord, threadWord, List.map_map]
  apply List.map_congr_left
  intro letter _
  cases letter <;> rfl

theorem toInstitutionCoreWord_mapTaggedWord (f : A ⟶ B)
    (word : TaggedWord A.CoreId A.ThreadId A.Event) :
    toInstitutionCoreWord (mapTaggedWord f.core f.thread f.event word) =
      Sig.Hom.mapCore f (toInstitutionCoreWord word) := by
  simp only [toInstitutionCoreWord, mapTaggedWord, Sig.Hom.mapCore, List.map_map]
  apply List.map_congr_left
  intro letter _
  cases letter <;> rfl

end Silmaril.Proofs.Machine.MulticoreVM.Placed
