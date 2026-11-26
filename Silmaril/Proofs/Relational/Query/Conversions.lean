module

public import Silmaril.Relational.Query.Defs
import Mathlib.Data.Set.Insert

public section

namespace Silmaril.Proofs.Relational.Query

open Silmaril.Relational

universe u v

variable {DB Query View Small Large : Type*} {Result : Type u}

theorem streamDrains_prefix {Cursor Row Error Final : Type*}
    {step : Cursor → StreamStep Cursor Row Error Final → Prop} {cursor : Cursor}
    {result : StreamResult Row Error Final} (run : StreamDrains step cursor result) :
    StreamPrefix step cursor result.rows := by
  induction run with
  | done => exact .nil _
  | error => exact .nil _
  | skip h _ tail => exact .skip h tail
  | yield h _ tail => exact .yield h tail

theorem ofPartial_toPartial_refines (sem : QueryRel DB Query Result) :
    (QueryRel.ofPartial sem.toPartial).Refines sem := by
  classical
  intro db query result observed
  change (if h : ∃ r, sem db query r then some (Classical.choose h) else none) =
    some result at observed
  split at observed
  · rename_i existsResult
    exact (Option.some.inj observed) ▸ Classical.choose_spec existsResult
  · contradiction

theorem ofPartial_toPartial (sem : QueryRel DB Query Result) (det : sem.Deterministic) :
    QueryRel.ofPartial sem.toPartial = sem := by
  classical
  funext db query result
  apply propext
  refine ⟨fun seen => ofPartial_toPartial_refines sem seen, fun observed => ?_⟩
  have existsResult : ∃ r, sem db query r := ⟨result, observed⟩
  change (if h : ∃ r, sem db query r then some (Classical.choose h) else none) = some result
  rw [dite_eq_left existsResult, det (Classical.choose_spec existsResult) observed]

theorem ofMonad_pure {M : Type u → Type v} [Pure M] (run : M Result → Set View)
    (view : Result → View) (law : ∀ result, run (pure result) = {view result})
    (eval : DB → Query → Result) :
    QueryRel.ofMonad run (fun db query => pure (eval db query)) =
      (QueryRel.ofTotal eval).observe view := by
  funext db query observed
  apply propext
  change observed ∈ run (pure (eval db query)) ↔ _
  rw [law, Set.mem_singleton_iff]
  exact ⟨fun h => ⟨_, rfl, h.symm⟩, fun ⟨result, h, seen⟩ => (congrArg view h).trans seen |>.symm⟩

theorem restrict_extend (embedding : Small ↪ Large) (sem : QueryRel DB Small Result) :
    (sem.extend embedding).restrict embedding = sem := by
  funext db small result
  apply propext
  exact ⟨fun ⟨other, h, observed⟩ => embedding.injective h ▸ observed,
    fun observed => ⟨small, rfl, observed⟩⟩

theorem extendQueries_apply_image {Value : Type*} (embedding : Small ↪ Large)
    (fallback : DB → Large → Value) (sem : DB → Small → Value) (db : DB) (small : Small) :
    extendQueries embedding fallback sem db (embedding small) = sem db small := by
  classical
  have existsSmall : ∃ other, embedding other = embedding small := ⟨small, rfl⟩
  unfold extendQueries
  rw [dite_eq_left existsSmall, embedding.injective (Classical.choose_spec existsSmall)]

theorem agreesOn_image_iff (translate : Small → Large) (left right : QueryRel DB Large Result) :
    left.AgreesOn (fun _ query => ∃ small, translate small = query) right ↔
      left.restrict translate = right.restrict translate := by
  constructor
  · intro agrees
    funext db small result
    exact propext (agrees (db := db) ⟨small, rfl⟩ result)
  · intro agrees db query ⟨small, eq⟩ result
    subst query
    exact Iff.of_eq (congrFun (congrFun (congrFun agrees db) small) result)

end Silmaril.Proofs.Relational.Query
