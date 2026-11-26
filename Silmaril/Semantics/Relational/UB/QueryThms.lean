module

public import Silmaril.Semantics.Relational.UB.QueryDefs
public import Silmaril.Semantics.Relational.UB.Thms
public import Silmaril.Semantics.Relational.Query.Thms
import Silmaril.Proofs.Semantics.Relational.UB.Queries

public section

namespace Silmaril.Relational.UB

variable {DB Query Result Reason Small Large : Type*}

namespace ExplicitQuery

@[simp] theorem forget_ofQueryRel (sem : QueryRel DB Query Result) :
    (ofQueryRel (Reason := Reason) sem).forget = sem := rfl

theorem forget_mono {impl spec : ExplicitQuery DB Query Result Reason} (refine : impl ≤ spec) :
    impl.forget.Refines spec.forget :=
  fun {db query _} seen => (refine db query).1 seen

/-- With no UB in the specification, refinement is exactly the absence of
implementation UB together with ordinary soundness. -/
theorem le_iff_of_safe {impl spec : ExplicitQuery DB Query Result Reason}
    (safe : ∀ db query, (spec db query).Safe) :
    impl ≤ spec ↔ (∀ db query, (impl db query).Safe) ∧ impl.forget.Refines spec.forget :=
  ⟨fun refine => ⟨fun db query => Explicit.safe_of_le (refine db query) (safe db query),
      forget_mono refine⟩,
    fun ⟨implSafe, sound⟩ db query => ⟨fun {result} seen => @sound db query result seen,
      (implSafe db query).trans (safe db query).symm |>.le⟩⟩

theorem collapse_mono {impl spec : ExplicitQuery DB Query Result Reason} (refine : impl ≤ spec) :
    impl.collapse ≤ spec.collapse :=
  fun db query => Explicit.collapse_monotone (refine db query)

theorem collapse_le_iff (impl spec : ExplicitQuery DB Query Result Reason) :
    impl.collapse ≤ spec.collapse ↔
      ∀ db query, ¬ (spec db query).Safe ∨ impl db query ≤ spec db query :=
  forall_congr' fun db => forall_congr' fun query => Explicit.collapse_le_collapse_iff
    (impl db query) (spec db query)

theorem restrict_mono {impl spec : ExplicitQuery DB Large Result Reason} (refine : impl ≤ spec)
    (translate : Small → Large) : impl.restrict translate ≤ spec.restrict translate :=
  fun db query => refine db (translate query)

theorem agreesOn_image_iff (translate : Small → Large)
    (left right : ExplicitQuery DB Large Result Reason) :
    left.AgreesOn (fun _ query => ∃ small, translate small = query) right ↔
      left.restrict translate = right.restrict translate :=
  (Proofs.Relational.UB.restrict_eq_iff translate left right).symm

@[simp] theorem restrict_extendUB (embedding : Small ↪ Large) (reason : Reason)
    (sem : ExplicitQuery DB Small Result Reason) :
    (sem.extendUB embedding reason).restrict embedding = sem :=
  funext fun db => funext fun query =>
    extendQueries_apply_image embedding (fun _ _ => Explicit.undefined reason) sem db query

theorem extendUB_apply_outside (embedding : Small ↪ Large) (reason : Reason)
    (sem : ExplicitQuery DB Small Result Reason) (db : DB) (query : Large)
    (outside : ¬ ∃ small, embedding small = query) :
    sem.extendUB embedding reason db query = Explicit.undefined reason :=
  extendQueries_apply_outside embedding _ sem db query outside

/-- The restriction accounts for refinements on the image. Outside it an
implementation must have empty ordinary results and only the specified reason. -/
theorem le_extendUB_iff (embedding : Small ↪ Large) (reason : Reason)
    (impl : ExplicitQuery DB Large Result Reason) (spec : ExplicitQuery DB Small Result Reason) :
    impl ≤ spec.extendUB embedding reason ↔ impl.restrict embedding ≤ spec ∧
      ∀ db query, (¬ ∃ small, embedding small = query) →
        impl db query ≤ Explicit.undefined reason :=
  Proofs.Relational.UB.le_extendQueries_iff embedding _ spec impl

@[simp] theorem forget_extendUB (embedding : Small ↪ Large) (reason : Reason)
    (sem : ExplicitQuery DB Small Result Reason) :
    (sem.extendUB embedding reason).forget = sem.forget.extend embedding :=
  Proofs.Relational.UB.forget_extendUB embedding reason sem

@[simp] theorem collapse_extendUB (embedding : Small ↪ Large) (reason : Reason)
    (sem : ExplicitQuery DB Small Result Reason) :
    (sem.extendUB embedding reason).collapse = sem.collapse.extendUB embedding :=
  Proofs.Relational.UB.collapse_extendUB embedding reason sem

end ExplicitQuery

namespace CatastrophicQuery

@[simp] theorem forget_ofQueryRel (sem : QueryRel DB Query Result) :
    (ofQueryRel sem).forget = sem := rfl

theorem restrict_mono {impl spec : CatastrophicQuery DB Large Result} (refine : impl ≤ spec)
    (translate : Small → Large) : impl.restrict translate ≤ spec.restrict translate :=
  fun db query => refine db (translate query)

theorem agreesOn_image_iff (translate : Small → Large)
    (left right : CatastrophicQuery DB Large Result) :
    left.AgreesOn (fun _ query => ∃ small, translate small = query) right ↔
      left.restrict translate = right.restrict translate :=
  (Proofs.Relational.UB.restrict_eq_iff translate left right).symm

@[simp] theorem restrict_extendUB (embedding : Small ↪ Large)
    (sem : CatastrophicQuery DB Small Result) :
    (sem.extendUB embedding).restrict embedding = sem :=
  funext fun db => funext fun query =>
    extendQueries_apply_image embedding (fun _ _ => ⊤) sem db query

theorem extendUB_apply_outside (embedding : Small ↪ Large)
    (sem : CatastrophicQuery DB Small Result) (db : DB) (query : Large)
    (outside : ¬ ∃ small, embedding small = query) :
    sem.extendUB embedding db query = ⊤ :=
  extendQueries_apply_outside embedding _ sem db query outside

/-- Refining a catastrophic extension imposes exactly the restricted comparison. -/
theorem le_extendUB_iff (embedding : Small ↪ Large) (impl : CatastrophicQuery DB Large Result)
    (spec : CatastrophicQuery DB Small Result) :
    impl ≤ spec.extendUB embedding ↔ impl.restrict embedding ≤ spec :=
  (Proofs.Relational.UB.le_extendQueries_iff embedding _ spec impl).trans
    ⟨And.left, fun refine => ⟨refine, fun _ _ _ => le_top⟩⟩

end CatastrophicQuery

end Silmaril.Relational.UB
