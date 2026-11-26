module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Thms
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

/-- Retain the emission, its literal attached readback, and the actual
opt-in versioned admission at the original public interface. -/
structure Compiled (g : ResultGrammar (L := exitList) source) where
  lowered : Lowered ports fields (g.toTable.toFlat List.length_ofFn)
  admission : Admission lowered
  ranked : admission.acyclicCheck = true

/-- Run the existing reverse emitter and checkers on the numbered witness.
The caller supplies internal label names. Ordered exits and live-out
registers are the fixed public interface of the source term. -/
def compile? [DecidableEq κ] [DecidableEq P.Instr] (g : ResultGrammar (L := exitList) source)
    (labels : Fin (g.toTable.size + 1) → K) : Option (Compiled g) := do
  let lowered ← lowerFresh labels context exits external fields (g.toTable.toFlat List.length_ofFn)
  if checked : Straight.packetLocalChecks lowered g.toTable.table.types = true then
    let admission := admit lowered g.toTable.table.types checked
    if ranked : admission.acyclicCheck = true then
      some ⟨lowered, admission, ranked⟩
    else none
  else none

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
noncomputable def Compiled.equation (c : Compiled g) : Equation P :=
  ⟨⟨n, context, B⟩, closedOperand (P := P) source.2,
    closedOperand (P := P) (c.admission.letCase c.ranked).2⟩

end Equation

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed
