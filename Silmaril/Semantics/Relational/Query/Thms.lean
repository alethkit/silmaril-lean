module

public import Silmaril.Semantics.Relational.Query.Defs
public import Mathlib.Data.Set.Insert
import Silmaril.Proofs.Semantics.Relational.Query.Conversions

@[expose] public section

namespace Silmaril.Relational

universe u v

theorem StreamDrains.prefix {Cursor Row Error Final : Type*}
    {step : Cursor → StreamStep Cursor Row Error Final → Prop} {cursor : Cursor}
    {result : StreamResult Row Error Final} (run : StreamDrains step cursor result) :
    StreamPrefix step cursor result.rows :=
  Proofs.Relational.Query.streamDrains_prefix run

namespace QueryRel

variable {DB Query View Small Large : Type*} {Result : Type u}
variable {impl spec other : QueryRel DB Query Result}

theorem Refines.refl (sem : QueryRel DB Query Result) : sem.Refines sem := fun h => h

theorem Refines.trans (h : impl.Refines spec) (k : spec.Refines other) : impl.Refines other :=
  fun seen => k (h seen)

theorem Refines.antisymm (h : impl.Refines spec) (k : spec.Refines impl) : impl = spec :=
  funext fun db => funext fun query => funext fun result => propext ⟨@h db query result, @k db query result⟩

theorem equivalent_iff_correct : impl.Equivalent spec ↔ impl.Sound spec ∧ impl.Complete spec :=
  ⟨fun h => ⟨fun seen => (h trivial _).mp seen, fun seen => (h trivial _).mpr seen⟩,
    fun ⟨sound, complete⟩ {db query} _ result => ⟨@sound db query result, @complete db query result⟩⟩

theorem equivalent_iff_eq : impl.Equivalent spec ↔ impl = spec :=
  equivalent_iff_correct.trans ⟨fun ⟨h, k⟩ => h.antisymm k, fun h => h ▸ ⟨Refines.refl _, Refines.refl _⟩⟩

theorem AgreesOn.mono {narrow wide : DB → Query → Prop}
    (h : impl.AgreesOn wide spec) (subset : ∀ {db query}, narrow db query → wide db query) :
    impl.AgreesOn narrow spec := fun admitted => h (subset admitted)

theorem AgreesOn.trans {fragment : DB → Query → Prop}
    (h : impl.AgreesOn fragment spec) (k : spec.AgreesOn fragment other) :
    impl.AgreesOn fragment other := fun admitted result => (h admitted result).trans (k admitted result)

theorem Refines.observe (h : impl.Refines spec) (view : Result → View) :
    (impl.observe view).Refines (spec.observe view) :=
  fun ⟨result, seen, observed⟩ => ⟨result, h seen, observed⟩

theorem AgreesOn.observe {fragment : DB → Query → Prop} (h : impl.AgreesOn fragment spec)
    (view : Result → View) : (impl.observe view).AgreesOn fragment (spec.observe view) :=
  fun admitted _ => exists_congr fun _ => and_congr_left' (h admitted _)

theorem Refines.deterministic (h : impl.Refines spec) (det : spec.Deterministic) :
    impl.Deterministic := fun left right => det (h left) (h right)

theorem Refines.total (h : impl.Refines spec) (total : impl.Total) : spec.Total :=
  fun db query => (total db query).imp fun _ seen => h seen

/-- Completeness is preserved when the specification shrinks. -/
theorem Complete.shrinkSpec (h : impl.Complete spec) (shrink : other.Refines spec) :
    impl.Complete other := shrink.trans h

/-- A total implementation that chooses only results of a deterministic specification
covers every specified result. -/
theorem complete_of_refines_of_total_of_deterministic (h : impl.Refines spec)
    (total : impl.Total) (det : spec.Deterministic) : impl.Complete spec :=
  fun {db query _} seen =>
    let ⟨_, actual⟩ := total db query
    det (h actual) seen ▸ actual

theorem ofStream_prefix {Cursor Row Error Final : Type*} (start : QueryRel DB Query Cursor)
    (step : Cursor → StreamStep Cursor Row Error Final → Prop) :
    ((ofStream start step).observe StreamResult.rows).Refines (streamPrefixes start step) :=
  fun ⟨_, ⟨cursor, started, drained⟩, eq⟩ => ⟨cursor, started, eq ▸ drained.prefix⟩

theorem ofTotal_deterministic (eval : DB → Query → Result) :
    (ofTotal eval).Deterministic := fun left right => left.symm.trans right

theorem ofTotal_total (eval : DB → Query → Result) : (ofTotal eval).Total :=
  fun _ _ => ⟨_, rfl⟩

theorem ofPartial_deterministic (eval : DB → Query → Option Result) :
    (ofPartial eval).Deterministic := fun left right => Option.some.inj (left.symm.trans right)

theorem ofPartial_total_iff (eval : DB → Query → Option Result) :
    (ofPartial eval).Total ↔ ∀ db query, (eval db query).isSome :=
  ⟨fun total db query => Option.isSome_iff_exists.mpr (total db query),
    fun total db query => Option.isSome_iff_exists.mp (total db query)⟩

theorem ofPartial_toPartial_refines (sem : QueryRel DB Query Result) :
    (ofPartial sem.toPartial).Refines sem :=
  Proofs.Relational.Query.ofPartial_toPartial_refines sem

/-- Determinism is exactly the condition for read-back of the chosen partial evaluator. -/
theorem ofPartial_toPartial (sem : QueryRel DB Query Result) (det : sem.Deterministic) :
    ofPartial sem.toPartial = sem :=
  Proofs.Relational.Query.ofPartial_toPartial sem det

theorem ofPartial_toPartial_iff (sem : QueryRel DB Query Result) :
    ofPartial sem.toPartial = sem ↔ sem.Deterministic :=
  ⟨fun h => h ▸ ofPartial_deterministic _, ofPartial_toPartial sem⟩

theorem ofTotal_toTotal_refines (sem : QueryRel DB Query Result) (total : sem.Total) :
    (ofTotal (sem.toTotal total)).Refines sem :=
  fun {db query _} observed => observed ▸ Classical.choose_spec (total db query)

theorem ofTotal_toTotal (sem : QueryRel DB Query Result) (total : sem.Total)
    (det : sem.Deterministic) : ofTotal (sem.toTotal total) = sem :=
  Refines.antisymm (ofTotal_toTotal_refines sem total)
    (complete_of_refines_of_total_of_deterministic (ofTotal_toTotal_refines sem total)
      (ofTotal_total _) det)

theorem exists_ofTotal_eq_iff (sem : QueryRel DB Query Result) :
    (∃ eval, ofTotal eval = sem) ↔ sem.Deterministic ∧ sem.Total :=
  ⟨fun ⟨eval, h⟩ => h ▸ ⟨ofTotal_deterministic eval, ofTotal_total eval⟩,
    fun ⟨det, total⟩ => ⟨sem.toTotal total, ofTotal_toTotal sem total det⟩⟩

@[simp] theorem ofNondet_toNondet (sem : QueryRel DB Query Result) :
    ofNondet sem.toNondet = sem := rfl

@[simp] theorem toNondet_ofNondet (eval : DB → Query → Set Result) :
    (ofNondet eval).toNondet = eval := rfl

/-- A runner that observes pure return as a singleton yields the total graph
through the chosen view. -/
theorem ofMonad_pure {M : Type u → Type v} [Pure M] (run : M Result → Set View)
    (view : Result → View) (law : ∀ result, run (pure result) = {view result})
    (eval : DB → Query → Result) :
    ofMonad run (fun db query => pure (eval db query)) = (ofTotal eval).observe view :=
  Proofs.Relational.Query.ofMonad_pure run view law eval

/-- If the runner reads bind as relational composition on the indicated types,
the query conversion preserves bind. -/
theorem ofMonad_bind {Next : Type u} {M : Type u → Type v} [Bind M]
    (run : M Result → Set Result) (runNext : M Next → Set View)
    (law : ∀ (action : M Result) (next : Result → M Next) (view : View),
      view ∈ runNext (action >>= next) ↔ ∃ result ∈ run action, view ∈ runNext (next result))
    (eval : DB → Query → M Result) (next : Result → M Next) :
    ofMonad runNext (fun db query => eval db query >>= next) =
      (ofMonad run eval).bindResults (fun result => runNext (next result)) :=
  funext fun db => funext fun query => funext fun view => propext (law (eval db query) next view)

theorem Refines.restrict {left right : QueryRel DB Large Result}
    (h : left.Refines right) (translate : Small → Large) :
    (left.restrict translate).Refines (right.restrict translate) := fun seen => h seen

theorem Refines.extend {left right : QueryRel DB Small Result}
    (h : left.Refines right) (translate : Small → Large) :
    (left.extend translate).Refines (right.extend translate) :=
  fun ⟨query, eq, seen⟩ => ⟨query, eq, h seen⟩

theorem extend_refines_iff (translate : Small → Large) (left : QueryRel DB Small Result)
    (right : QueryRel DB Large Result) :
    (left.extend translate).Refines right ↔ left.Refines (right.restrict translate) :=
  ⟨fun h {_ _ _} seen => h ⟨_, rfl, seen⟩,
    fun h {_ _ _} ⟨_, eq, seen⟩ => eq ▸ h seen⟩

@[simp] theorem restrict_extend (embedding : Small ↪ Large) (sem : QueryRel DB Small Result) :
    (sem.extend embedding).restrict embedding = sem :=
  Proofs.Relational.Query.restrict_extend embedding sem

theorem agreesOn_image_iff (translate : Small → Large) (left right : QueryRel DB Large Result) :
    left.AgreesOn (fun _ query => ∃ small, translate small = query) right ↔
      left.restrict translate = right.restrict translate :=
  Proofs.Relational.Query.agreesOn_image_iff translate left right

end QueryRel

namespace StatefulQueryRel

variable {DB Query Result : Type*}

@[simp] theorem ofQueryRel_toQueryRel (sem : StatefulQueryRel DB Query Result) :
    ofQueryRel sem.toQueryRel = sem := rfl

@[simp] theorem toQueryRel_ofQueryRel (sem : QueryRel DB Query (Result × DB)) :
    (ofQueryRel sem).toQueryRel = sem :=
  funext fun _ => funext fun _ => funext fun ⟨_, _⟩ => rfl

theorem forgetState_iff (sem : StatefulQueryRel DB Query Result) (db : DB)
    (query : Query) (result : Result) :
    sem.forgetState db query result ↔ ∃ finalDB, sem db query result finalDB :=
  ⟨fun ⟨⟨_, finalDB⟩, seen, eq⟩ => ⟨finalDB, eq ▸ seen⟩,
    fun ⟨finalDB, seen⟩ => ⟨(result, finalDB), seen, rfl⟩⟩

@[simp] theorem forgetState_ofReadOnly (sem : QueryRel DB Query Result) :
    (ofReadOnly sem).forgetState = sem :=
  funext fun db => funext fun query => funext fun result => propext
    ((forgetState_iff (ofReadOnly sem) db query result).trans
      ⟨fun ⟨_, seen, _⟩ => seen, fun seen => ⟨db, seen, rfl⟩⟩)

@[simp] theorem toQueryRel_ofStateM {State Value : Type u} (eval : Query → StateM State Value) :
    (ofStateM eval).toQueryRel = QueryRel.ofTotal (fun db query => (eval query).run db) :=
  toQueryRel_ofQueryRel _

end StatefulQueryRel

@[simp] theorem extendQueries_apply_image {DB Small Large Value : Type*} (embedding : Small ↪ Large)
    (fallback : DB → Large → Value) (sem : DB → Small → Value) (db : DB) (small : Small) :
    extendQueries embedding fallback sem db (embedding small) = sem db small :=
  Proofs.Relational.Query.extendQueries_apply_image embedding fallback sem db small

theorem extendQueries_apply_outside {DB Small Large Value : Type*} (embedding : Small ↪ Large)
    (fallback : DB → Large → Value) (sem : DB → Small → Value) (db : DB) (query : Large)
    (outside : ¬ ∃ small, embedding small = query) :
    extendQueries embedding fallback sem db query = fallback db query := by
  unfold extendQueries
  rw [dite_eq_right outside]

end Silmaril.Relational
