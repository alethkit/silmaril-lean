module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Defs

/-! # Bounded current-table discovery and replay for zero sampling -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist

open PEG

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable [DecidableEq Data] [DecidableEq (P [] .count)]

/-- Match an actual zero-sample redex that still lacks an exact RHS
in its class. Unmatched rows are ineligible. -/
def enabled (zero : P [] .count) (s : Output P params results l) (i : Fin s.1) : Bool :=
  match ZeroSample.matchAt (g := s.2.graph) i zero with
  | none => false
  | some found => !checkCovered found s.2.classes

def enabledAt (zero : P [] .count) (s : Output P params results l) (address : Nat) : Bool :=
  if bound : address < s.1 then enabled zero s ⟨address, bound⟩ else false

def next (zero : P [] .count) (s : Output P params results l) : Option (Fin s.1) :=
  (List.finRange s.1).find? (enabled zero s)

def checkFixed (zero : P [] .count) (s : Output P params results l) : Bool :=
  (next zero s).isNone

/-- All actual matches in the current table have a covered RHS. -/
def Fixed (zero : P [] .count) (s : Output P params results l) : Prop :=
  ∀ (i : Fin s.1) (found : ZeroSample s.2.graph i zero), Covered found s.2.classes

/-- The family of visits uses the same policy as the executable driver. -/
def Visits (zero : P [] .count) : NormalForms.Family (Output P params results l) Nat :=
  fun address s target => target = visit zero s address

inductive Stop where
  | fixed
  | exhausted
  deriving DecidableEq

structure Report where
  sites : List Nat
  stop : Stop

structure Result (P : InstructionSet.{u,v} Data) (params results : List (Ty Data)) (l : Nat) where
  state : Output P params results l
  report : Report

/-- Check for closure even when no transition fuel remains. Charge only
an enabled visit. Every successful transition starts a new table scan. -/
def run (zero : P [] .count) : Nat → Output P params results l → Result P params results l
  | fuel, s =>
    match next zero s with
    | none => ⟨s, ⟨[], .fixed⟩⟩
    | some i =>
      match fuel with
      | 0 => ⟨s, ⟨[], .exhausted⟩⟩
      | fuel + 1 =>
        let rest := run zero fuel (visit zero s i.val)
        ⟨rest.state, ⟨i.val :: rest.report.sites, rest.report.stop⟩⟩
termination_by structural fuel _ => fuel

/-- Accept any chronological sequence of enabled visits. Discovery order
is a policy of `run`; replay checks the supplied addresses directly. -/
def replay (zero : P [] .count) : Output P params results l → List Nat → Option (Output P params results l)
  | s, [] => some s
  | s, i :: rest =>
    if enabledAt zero s i then replay zero (visit zero s i) rest else none

/-- A portable receipt contains addresses and a stop claim. Recompute the
state and validate the budget and stop claim on the final table. -/
def checkStop (zero : P [] .count) (fuel : Nat) (state : Output P params results l)
    (report : Report) : Bool :=
  match report.stop with
  | .fixed => checkFixed zero state
  | .exhausted => decide (report.sites.length = fuel) && !checkFixed zero state

def check (zero : P [] .count) (fuel : Nat) (source : Output P params results l)
    (report : Report) : Option (Output P params results l) :=
  if report.sites.length ≤ fuel then
    match replay zero source report.sites with
    | none => none
    | some state => if checkStop zero fuel state report then some state else none
  else none

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
