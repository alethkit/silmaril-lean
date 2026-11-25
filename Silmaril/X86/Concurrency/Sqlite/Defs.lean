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

/-- An implementation label may emit one event or be silent. The separate
byte footprint includes hidden memory accesses. Its interpretation is fixed
when comparing candidate relations. -/
structure Projection (layer : Layer) (Label Final : Type) where
  event : Label → Option layer.Event
  final : Final → layer.Final
  bytes : Label → Set Nat

def Projection.observe {layer : Layer} {Label Final : Type}
    (p : Projection layer Label Final) (run : List Label × Final) : layer.Observation :=
  (run.1.filterMap p.event, p.final run.2)

abbrev Proposal (Input : Type) (layer : Layer) := Set (Input × layer.Input)

/-- Every admitted x86 run projects to a VM run and every byte it accesses
lies in the allowed footprint for this pair. Candidate relations are ordered
by inclusion as sets of input pairs. -/
def Sound {Input Label Final : Type} {layer : Layer}
    (runs : Input → Set (List Label × Final)) (p : Projection layer Label Final)
    (allowed : Input → layer.Input → Set Nat) (proposed : Proposal Input layer) : Prop :=
  ∀ pair ∈ proposed, ∀ run ∈ runs pair.1,
    p.observe run ∈ layer.behaviors pair.2 ∧
      ∀ label ∈ run.1, p.bytes label ⊆ allowed pair.1 pair.2

/-- Byte spans at instruction issue. Propagation of pending stores is a
separate obligation for a buffered implementation. -/
def accessBytes : Tso.XEvent Nat → Set Nat
  | .load _ a bs | .store _ a bs => { b | a ≤ b ∧ b < a + bs.length }
  | .rmw _ a old new => { b | a ≤ b ∧ b < a + max old.length new.length }
  | .fence _ => ∅

/-- Operational SC for the chosen interleaved instruction traces. -/
def scRuns (traces : Set (List (Tso.XEvent Nat))) (initial : Tso.Mem) :
    Set (List (Tso.XEvent Nat) × Tso.Mem) :=
  { run | run.1 ∈ traces ∧ Tso.Execution Tso.SCStep initial run.1 run.2 }

/-- Operational FIFO byte TSO for the same traces. Weak steps allow silent
flushes before and after each instruction. The final state retains buffers. -/
def tsoRuns (traces : Set (List (Tso.XEvent Nat))) (initial : Tso.XState Nat) :
    Set (List (Tso.XEvent Nat) × Tso.XState Nat) :=
  { run | run.1 ∈ traces ∧ Tso.Execution Tso.XWeakStep initial run.1 run.2 }

/-- Axiomatic candidates under the named model, including SC, strict TSO and
XL. The chosen traces are indexed by thread. This vector gives no interleaving
order for visible events across threads. -/
def axiomaticRuns (model : Lattice.Name) (test : MemoryModel.Litmus.Test)
    (choices : List (List MemoryModel.Litmus.XTrace)) : Set (List MemoryModel.Litmus.XTrace × MemoryModel.Litmus.Final) :=
  { run | List.Forall₂ (· ∈ ·) run.1 choices ∧
    MemoryModel.Litmus.AxReach test (run.1.map fun trace => [trace]) model.model run.2 }

end Silmaril.X86.Concurrency.Sqlite
