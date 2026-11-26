module

public import Silmaril.Semantics.Page.Trace.Defs
import Silmaril.Proofs.Semantics.Page.Trace.Laws

/-! Replay composition, projections, framing and correspondence with page programs. -/

public section
namespace Silmaril.Semantics.Page

universe u v w x y
variable {Id : Type u} {Content : Type v} {Memory : Type w} {Other : Type x} {access : Access Id Content Memory}
variable {trace first last : Trace Id Content} {page : Id}
variable {initial middle final : Memory}

theorem Trace.reads_append :
    (first ++ last).reads = first.reads ++ last.reads :=
  Proofs.Semantics.Page.reads_append

theorem Trace.writes_append :
    (first ++ last).writes = first.writes ++ last.writes :=
  Proofs.Semantics.Page.writes_append

theorem ReadTrace.reads_toTrace (reads : ReadTrace Id Content) :
    reads.toTrace.reads = reads :=
  Proofs.Semantics.Page.reads_toTrace reads

theorem WriteTrace.writes_toTrace (writes : WriteTrace Id Content) :
    writes.toTrace.writes = writes :=
  Proofs.Semantics.Page.writes_toTrace writes

theorem Trace.readOnly_reads (trace : Trace Id Content) : trace.reads.toTrace.ReadOnly :=
  Proofs.Semantics.Page.readOnly_reads trace

theorem Trace.writeOnly_writes (trace : Trace Id Content) : trace.writes.toTrace.WriteOnly :=
  Proofs.Semantics.Page.writeOnly_writes trace

theorem Trace.defs_append :
    (first ++ last).Defs page ↔ first.Defs page ∨ last.Defs page :=
  Proofs.Semantics.Page.defs_append

theorem Trace.footprint_append :
    (first ++ last).Footprint page ↔ first.Footprint page ∨ last.Footprint page :=
  Proofs.Semantics.Page.footprint_append

theorem Trace.uses_append :
    (first ++ last).Uses page ↔ first.Uses page ∨ (¬ first.Defs page ∧ last.Uses page) :=
  Proofs.Semantics.Page.uses_append

theorem Trace.uses_or_defs : trace.Uses page ∨ trace.Defs page ↔ trace.Footprint page :=
  Proofs.Semantics.Page.uses_or_defs

theorem Trace.replays_append :
    (first ++ last).Replays access initial final ↔
      ∃ middle, first.Replays access initial middle ∧ last.Replays access middle final :=
  Proofs.Semantics.Page.replays_append

theorem Trace.run_eq_some_iff [DecidableEq Content] :
    trace.run access initial = some final ↔ trace.Replays access initial final :=
  Proofs.Semantics.Page.run_eq_some_iff

theorem Trace.Replays.unique (left : trace.Replays access initial middle)
    (right : trace.Replays access initial final) : middle = final :=
  Proofs.Semantics.Page.replays_unique left right

theorem Trace.replays_map {other : Access Id Content Other} (f : Memory → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f)
    {target : Other} :
    trace.Replays other (f initial) target ↔
      ∃ final, trace.Replays access initial final ∧ f final = target :=
  Proofs.Semantics.Page.replays_map f read write

theorem Trace.run_map [DecidableEq Content] {other : Access Id Content Other} (f : Memory → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f) :
    trace.run other (f initial) = (trace.run access initial).map f :=
  Proofs.Semantics.Page.run_map f read write

theorem ReadTrace.replays_iff (reads : ReadTrace Id Content) :
    reads.toTrace.Replays access initial final ↔ initial = final ∧ reads.Agrees access initial :=
  Proofs.Semantics.Page.replays_readTrace reads

theorem Trace.Replays.writes (run : trace.Replays access initial final) :
    trace.writes.toTrace.Replays access initial final :=
  Proofs.Semantics.Page.replays_writes run

theorem Store.access_write_iff {store : Store Id Content Memory} {value : Content} :
    store.access.write initial page value = some middle ↔
      store.domain initial page ∧ store.set initial page (.defined value) = middle :=
  Proofs.Semantics.Page.store_write_iff

theorem Store.access_read_iff {store : Store Id Content Memory} {value : Content} :
    store.access.read initial page = some value ↔ store.lookup initial page = .defined value :=
  Proofs.Semantics.Page.store_read_iff

theorem Trace.Replays.frame {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final) (outside : ¬ trace.Defs page) :
    store.lookup final page = store.lookup initial page :=
  Proofs.Semantics.Page.replays_frame run outside

theorem Trace.Replays.use_defined {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final) (used : trace.Uses page) :
    ∃ value, store.lookup initial page = .defined value :=
  Proofs.Semantics.Page.replays_use_defined run used

theorem Trace.Replays.reads_agree_of_disjoint {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final)
    (disjoint : ∀ p, trace.Reads p → ¬ trace.Defs p) :
    trace.reads.Agrees store.access initial :=
  Proofs.Semantics.Page.reads_agree_of_disjoint run disjoint

theorem Trace.Replays.reads_of_disjoint {store : Store Id Content Memory}
    (run : trace.Replays store.access initial final)
    (disjoint : ∀ p, trace.Reads p → ¬ trace.Defs p) :
    trace.reads.toTrace.Replays store.access initial initial :=
  (ReadTrace.replays_iff _).mpr ⟨rfl, run.reads_agree_of_disjoint disjoint⟩

theorem Program.Records.run {Result : Type y} {M : Model Id Content Memory} {program : Program Id Content Result}
    {result : Result} (path : Program.Records program trace result)
    (run : trace.Replays M.store.access initial final) :
    Run M program initial trace.writes.edits (.returned result final) :=
  Proofs.Semantics.Page.records_run path run

theorem Trace.Replays.completion [DecidableEq Id] {M : Model Id Content Memory}
    {image : Image Id Content} (run : trace.Replays M.store.access initial final)
    (complete : Completion M initial image) :
    ∃ target, Replay trace.writes.edits image target ∧ Completion M final target :=
  Proofs.Semantics.Page.replay_completion run complete

end Silmaril.Semantics.Page
