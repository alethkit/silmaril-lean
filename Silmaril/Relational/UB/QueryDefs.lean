module

public import Silmaril.Relational.Query.Defs
public import Silmaril.Relational.UB.Defs

/-!
# UB indexed by database and query

These types carry the pointwise orders. Ordinary result completeness is
reverse result inclusion, so shrinking an implementation can lose
completeness even when it preserves totality. With explicit UB, the order
also requires inclusion of the reason sets. With catastrophic UB the order
imposes no result requirement at a catastrophic specification input.
-/

@[expose] public section

namespace Silmaril.Relational.UB

abbrev ExplicitQuery (DB Query Result Reason : Type*) :=
  DB → Query → Explicit Result Reason

abbrev CatastrophicQuery (DB Query Result : Type*) :=
  DB → Query → Catastrophic Result

variable {DB Query Result Reason Small Large : Type*}

namespace ExplicitQuery

def ofQueryRel (sem : QueryRel DB Query Result) : ExplicitQuery DB Query Result Reason :=
  fun db query => Explicit.defined (sem.toNondet db query)

def forget (sem : ExplicitQuery DB Query Result Reason) : QueryRel DB Query Result :=
  QueryRel.ofNondet fun db query => (sem db query).forget

noncomputable def collapse (sem : ExplicitQuery DB Query Result Reason) :
    CatastrophicQuery DB Query Result :=
  fun db query => (sem db query).collapse

def restrict (translate : Small → Large) (sem : ExplicitQuery DB Large Result Reason) :
    ExplicitQuery DB Small Result Reason :=
  fun db query => sem db (translate query)

/-- Tag every query outside the embedded image with the given UB reason. -/
noncomputable def extendUB (embedding : Small ↪ Large) (reason : Reason)
    (sem : ExplicitQuery DB Small Result Reason) : ExplicitQuery DB Large Result Reason :=
  extendQueries embedding (fun _ _ => Explicit.undefined reason) sem

/-- Agreement requires equality of both observable results and UB reasons. -/
abbrev AgreesOn (fragment : DB → Query → Prop)
    (left right : ExplicitQuery DB Query Result Reason) : Prop :=
  ∀ db query, fragment db query → left db query = right db query

end ExplicitQuery

namespace CatastrophicQuery

/-- Embed a result relation as a defined semantics at every input. -/
def ofQueryRel (sem : QueryRel DB Query Result) : CatastrophicQuery DB Query Result :=
  fun db query => .defined (sem.toNondet db query)

def forget (sem : CatastrophicQuery DB Query Result) : QueryRel DB Query Result :=
  QueryRel.ofNondet fun db query => (sem db query).forget

def restrict (translate : Small → Large) (sem : CatastrophicQuery DB Large Result) :
    CatastrophicQuery DB Small Result :=
  fun db query => sem db (translate query)

/-- Use catastrophic UB at every query outside the embedded image. -/
noncomputable def extendUB (embedding : Small ↪ Large) (sem : CatastrophicQuery DB Small Result) :
    CatastrophicQuery DB Large Result :=
  extendQueries embedding (fun _ _ => ⊤) sem

/-- Agreement preserves the distinction between catastrophic UB and defined results. -/
abbrev AgreesOn (fragment : DB → Query → Prop) (left right : CatastrophicQuery DB Query Result) :
    Prop :=
  ∀ db query, fragment db query → left db query = right db query

end CatastrophicQuery

end Silmaril.Relational.UB
