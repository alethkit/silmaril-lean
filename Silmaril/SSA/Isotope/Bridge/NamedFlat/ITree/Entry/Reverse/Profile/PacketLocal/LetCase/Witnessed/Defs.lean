module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Institution.Defs

/-! # Admit an independently witnessed LetCase term as named packet-local RTL -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed

open LambdaSSA (Region)
open LambdaSSA.Acyclic
open LambdaSSA.Acyclic.Positional.Capture.Reverse
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Isotope.Institution.LetCase.WeakITree (Equation closedOperand)

universe u v

variable {κ K : Type (u + 1)} [DecidableEq K] {n : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}

local notation "ports" => numberedInterface context exits external
local notation "exitTypes" => Interface.external (LiveOut.exitInterface ports fields)
local notation "exitList" => List.ofFn exitTypes
local notation "B" => Region.packedExitType exitList

variable {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))}

/-- The actual table handed to the named emitter. The optional slot is
from the original caller context and is carried only on internal edges. -/
def flat (g : ResultGrammar (L := exitList) source) :
    Option (Fin n) → LambdaSSA.FiniteCFG P.Instr (g.toTable.size + 1) exits.length n
  | none => g.toTable.toFlat List.length_ofFn
  | some slot => Capture.Carry.graph (g.toTable.toFlat List.length_ofFn) slot

/-- The internal packet types of the table handed to the emitter. -/
def packetTypes (g : ResultGrammar (L := exitList) source) :
    Option (Fin n) → Fin (g.toTable.size + 1) → Ty κ
  | none => g.toTable.table.types
  | some slot => Capture.Carry.packetTypes g.toTable.table.types context slot

/-- Retain the emission, its literal attached readback, and the actual
opt-in versioned admission at the original public interface. -/
structure Compiled (g : ResultGrammar (L := exitList) source) (slot : Option (Fin n) := none) where
  lowered : Lowered ports fields (flat g slot)
  admission : Admission lowered
  ranked : admission.acyclicCheck = true

/-- Check typing, actual opt-in reversion and entry-reachable rank after emission. -/
def checkAdmission [DecidableEq κ] (g : ResultGrammar (L := exitList) source)
    {slot : Option (Fin n)} (lowered : Lowered ports fields (flat g slot)) :
    Option (Compiled g slot) :=
  if checked : Straight.packetLocalChecks lowered (packetTypes g slot) = true then
    let admission := admit lowered (packetTypes g slot) checked
    if ranked : admission.acyclicCheck = true then some ⟨lowered, admission, ranked⟩ else none
  else none

/-- Run the existing reverse emitter and checkers on the numbered witness. -/
def compile? [DecidableEq κ] [DecidableEq P.Instr] (g : ResultGrammar (L := exitList) source)
    (labels : Fin (g.toTable.size + 1) → K) : Option (Compiled g) := do
  let lowered ← lowerFresh labels context exits external fields (flat g none)
  checkAdmission g (slot := none) lowered

/-- Carry a caller slot explicitly in each internal packet before running
the same emitter and checkers. The register plan must reproduce the selected
live-out reads exactly after the new packet decoder. -/
def compileCarry? [DecidableEq κ] [DecidableEq P.Instr] (g : ResultGrammar (L := exitList) source)
    (slot : Fin n) (registers : Registers Register) (labels : Fin (g.toTable.size + 1) → K) :
    Option (Compiled g (some slot)) := do
  let lowered ← lowerChecked ports fields registers labels (flat g (some slot))
  checkAdmission g (slot := some slot) lowered

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

/-- Native evaluation of the original written term at the shared caller record. -/
noncomputable def sourceTree (M : Model (κ := κ) Events P.Instr) (source : Operand P.Instr context B)
    (x : Record.Input context) : ModelTree Events (Ty.denote C B) :=
  source.2.denote (Ty.denote C) ⟨M.instructions.denote⟩ (fun y => y.elim) (Record.field context x)

section Equation

variable {P : FlatInstitution.Signature.{u, u+1} κ}
  {source : Operand P.Instr context (Region.packedExitType
    (List.ofFn (LiveOut.exitInterface (numberedInterface context exits external) fields).external))} {g : ResultGrammar source}

/-- Compare the written source with the LetCase expansion of the actual
admitted packed graph, using the existing exact institution's sentence. -/
noncomputable def Compiled.equation {slot : Option (Fin n)} (c : Compiled g slot) : Equation P :=
  ⟨⟨n, context, B⟩, closedOperand (P := P) source.2,
    closedOperand (P := P) (c.admission.letCase c.ranked).2⟩

end Equation

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed
