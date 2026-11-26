module

public import Silmaril.Machine.MulticoreVM.Placed.Defs
public import Silmaril.Machine.MulticoreVM.Institution.Defs

@[expose] public section

namespace Silmaril.Machine.MulticoreVM.Placed

open Institution (Sig)

universe u

variable {A : Sig.{u}}

/-- The institutional core-tagged word keeps the core tag and the whole thread letter.
A sync's executing thread tag is omitted, while its participant list is preserved. -/
def toInstitutionCoreWord (word : TaggedWord A.CoreId A.ThreadId A.Event) : A.CoreWord :=
  word.map fun
    | .event core thread value => (core, .event thread value)
    | .sync core _ participants => (core, .sync participants)

/-- Erase the emitting core from each letter of the institution's core-tagged profile. -/
def forgetInstitutionCore (word : A.CoreWord) : A.NamedWord := word.map Prod.snd

end Silmaril.Machine.MulticoreVM.Placed
