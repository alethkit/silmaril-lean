module

public import Silmaril.Semantics.Page.Array.Defs
public import Silmaril.Semantics.Page.Trace.Thms
import Silmaril.Proofs.Semantics.Page.Array.Laws

/-! Array embeddings preserve reads, writes and chronological replay. -/

public section
namespace Silmaril.Semantics.Page

universe v
variable {Content : Type v} {n : Nat} {trace : Trace Nat Content}

theorem Array.embed_read (a : Array n Content) (page : Nat) :
    (UndefArray.access n Content).read a.embed page = (Array.access n Content).read a page :=
  Proofs.Semantics.Page.embed_read a page

theorem Array.embed_write (a : Array n Content) (page : Nat) (v : Content) :
    (UndefArray.access n Content).write a.embed page v =
      ((Array.access n Content).write a page v).map Array.embed :=
  Proofs.Semantics.Page.embed_write a page v

theorem UndefArray.memory_read (a : UndefArray n Content) (page : Nat) :
    (mapStore Nat Content).access.read a.toMemory page = (UndefArray.access n Content).read a page :=
  Proofs.Semantics.Page.memory_read a page

theorem UndefArray.memory_write (a : UndefArray n Content) (page : Nat) (v : Content) :
    (mapStore Nat Content).access.write a.toMemory page v =
      ((UndefArray.access n Content).write a page v).map UndefArray.toMemory :=
  Proofs.Semantics.Page.memory_write a page v

/-- Running a trace commutes with embedding, including rejection. -/
theorem Trace.run_embed [DecidableEq Content] (a : Array n Content) :
    trace.run (UndefArray.access n Content) a.embed =
      (trace.run (Array.access n Content) a).map Array.embed :=
  Trace.run_map Array.embed Array.embed_read Array.embed_write

theorem Trace.run_memory [DecidableEq Content] (a : UndefArray n Content) :
    trace.run (mapStore Nat Content).access a.toMemory =
      (trace.run (UndefArray.access n Content) a).map UndefArray.toMemory :=
  Trace.run_map UndefArray.toMemory UndefArray.memory_read UndefArray.memory_write

/-- Replay on the embedded total array gives exactly the embedded total result. -/
theorem Trace.replays_embed_iff {a b : Array n Content} :
    trace.Replays (UndefArray.access n Content) a.embed b.embed ↔
      trace.Replays (Array.access n Content) a b :=
  Proofs.Semantics.Page.replays_embed_iff

theorem Trace.replays_memory_iff {a b : UndefArray n Content} :
    trace.Replays (mapStore Nat Content).access a.toMemory b.toMemory ↔
      trace.Replays (UndefArray.access n Content) a b :=
  Proofs.Semantics.Page.replays_memory_iff

/-- Filling UNDEF carries a successful replay to total arrays using the same
fill at both endpoints. It may admit additional reads. -/
theorem Trace.Replays.complete {a b : UndefArray n Content}
    (run : trace.Replays (UndefArray.access n Content) a b) (fill : Array n Content) :
    trace.Replays (Array.access n Content) (a.complete fill) (b.complete fill) :=
  Proofs.Semantics.Page.replays_complete run fill

theorem Trace.satisfiable_iff (fill : Array n Content) :
    trace.UndefArraySatisfiable n ↔ trace.ArraySatisfiable n :=
  Proofs.Semantics.Page.satisfiable_iff fill

/-- Every successful replay, including a read after a write, stays in bounds. -/
theorem Trace.Replays.undef_inBounds {a b : UndefArray n Content}
    (run : trace.Replays (UndefArray.access n Content) a b) : trace.InBounds n :=
  Proofs.Semantics.Page.undef_replay_inBounds run

theorem Trace.Replays.array_inBounds {a b : Array n Content}
    (run : trace.Replays (Array.access n Content) a b) : trace.InBounds n :=
  (Trace.replays_embed_iff.mpr run).undef_inBounds

end Silmaril.Semantics.Page
