module

public import Silmaril.Formats.Sqlite.Vdbe.Defs
public import Silmaril.Machine.SqliteControl.Defs
public import Silmaril.X86.MemoryModel.Lattice.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Defs

/-! # Finite x86-to-SQLite translation relations

The implementation is x86 and the specification is the selected SQLite tier.
Soundness requires every admitted implementation run of a paired input to
have its projected observations in the specification. The footprint check
also sees actions erased by the projection. This specification imposes no
progress or initial-state inhabitation requirement.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Sqlite

open Silmaril.Formats.Sqlite (Value)
open Silmaril.Formats.Sqlite.Vdbe (Database Program Trace)
open Silmaril.Machine.SqliteControl (Call CallStep Config Phase Run Shared Step)
open Silmaril.X86.MemoryModel

/-- Existing SQLite semantics, at the source call, abstract control or bytecode boundary. -/
inductive Layer where
  | call
  | control
  | vdbe

structure VdbeInput where
  database : Database
  program : Program
  initial : Formats.Sqlite.Vdbe.State

def Layer.Input : Layer → Type
  | .call => Config Call
  | .control => Config Phase
  | .vdbe => VdbeInput

def Layer.Event : Layer → Type
  | .call | .control => Machine.SqliteControl.Event
  | .vdbe => List Value

/-- The shared-state observation or, for bytecode, the optional halt status of a prefix. -/
def Layer.Final : Layer → Type
  | .call | .control => Shared
  | .vdbe => Option Nat

abbrev Layer.Observation (layer : Layer) := List layer.Event × layer.Final

/-- All finite prefixes. Bytecode observes only rows emitted after the given initial state.
The landed VDBE trace is the successful relational step closure. -/
def Layer.behaviors : (layer : Layer) → layer.Input → Set layer.Observation
  | .call, initial => { obs | ∃ final, Run CallStep initial obs.1 final ∧ final.shared = obs.2 }
  | .control, initial => { obs | ∃ final, Run Step initial obs.1 final ∧ final.shared = obs.2 }
  | .vdbe, input => { obs | ∃ final, Trace input.database input.program input.initial final ∧
      final.rows = List.append input.initial.rows obs.1 ∧ final.halted = obs.2 }

/-- An implementation label may emit one event or be silent. -/
structure Projection (layer : Layer) (Label Final : Type) where
  event : Label → Option layer.Event
  final : Final → layer.Final

abbrev Proposal (Input : Type) (layer : Layer) := Set (Input × layer.Input)

/-- Byte spans at instruction issue. Propagation of pending stores is a
separate obligation for a buffered implementation. -/
def accessBytes : Tso.XEvent Nat → Set Nat
  | .load _ a bs | .store _ a bs => { b | a ≤ b ∧ b < a + bs.length }
  | .rmw _ a old new => { b | a ≤ b ∧ b < a + max old.length new.length }
  | .fence _ => ∅

/-- The union of issued access spans, including every unobserved access. -/
def issuedBytes (labels : List (Tso.XEvent Nat)) : Set Nat :=
  { addr | ∃ label ∈ labels, addr ∈ accessBytes label }

/-- Axiomatic candidate units covering the byte. `Litmus.AxReach` requires the
candidate's events to be exactly these units. Fence events have no span here. -/
def candidateBytes (traces : List MemoryModel.Litmus.XTrace) : Set Nat :=
  { addr | ∃ unit ∈ (MemoryModel.Litmus.units traces).map Prod.fst,
    (unit.isR || unit.isW) = true ∧ unit.covers addr = true }


/-- Operational SC and FIFO TSO have interleaved labels. The axiomatic trace
vector is indexed by thread and provides no ordering across threads. -/
inductive MemorySemantics where
  | sc
  | fifo
  | axiomatic (model : Lattice.Name)

def MemorySemantics.Initial : MemorySemantics → Type
  | .sc => Tso.Mem
  | .fifo => Tso.XState Nat
  | .axiomatic _ => MemoryModel.Litmus.Test

def MemorySemantics.Label : MemorySemantics → Type
  | .sc | .fifo => Tso.XEvent Nat
  | .axiomatic _ => MemoryModel.Litmus.XTrace

def MemorySemantics.Final : MemorySemantics → Type
  | .sc => Tso.Mem
  | .fifo => Tso.XState Nat
  | .axiomatic _ => MemoryModel.Litmus.Final

structure Execution (semantics : MemorySemantics) where
  labels : List semantics.Label
  final : semantics.Final

/-- Validate the record against the selected semantics. FIFO weak steps
permit silent flushes around each label and retain the final buffers. The
axiomatic case checks exactly the given per-thread trace choices. -/
def MemorySemantics.Executes : (model : MemorySemantics) → model.Initial → Execution model → Prop
  | .sc, initial, run => Tso.Execution Tso.SCStep initial run.labels run.final
  | .fifo, initial, run => Tso.Execution Tso.XWeakStep initial run.labels run.final
  | .axiomatic model, test, run =>
    MemoryModel.Litmus.AxReach test (run.labels.map fun trace => [trace]) model.model run.final

/-- Computed before observation. Admitting or hiding a label cannot change its access span. -/
def Execution.bytes : {model : MemorySemantics} → Execution model → Set Nat
  | .sc, run => issuedBytes run.labels
  | .fifo, run => issuedBytes run.labels
  | .axiomatic _, run => candidateBytes run.labels

def Projection.observe {layer : Layer} {model : MemorySemantics}
    (p : Projection layer model.Label model.Final) (run : Execution model) : layer.Observation :=
  (run.labels.filterMap p.event, p.final run.final)

/-- Every admitted execution of the selected memory semantics projects to a
SQLite run. Its computed footprint is included in the bytes allowed for the
input pair. The admission predicate can select executions. It cannot supply a
different execution semantics or footprint. -/
def Sound {Input : Type} {layer : Layer} (model : MemorySemantics)
    (initial : Input → model.Initial) (admitted : Input → Execution model → Prop)
    (p : Projection layer model.Label model.Final) (allowed : Input → layer.Input → Set Nat)
    (proposed : Proposal Input layer) : Prop :=
  ∀ pair ∈ proposed, ∀ run, model.Executes (initial pair.1) run → admitted pair.1 run →
    p.observe run ∈ layer.behaviors pair.2 ∧ run.bytes ⊆ allowed pair.1 pair.2

end Silmaril.X86.Concurrency.Sqlite
