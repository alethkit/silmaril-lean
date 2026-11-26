module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Thms

/-! # Opt-in packet-local reversion at the original typed interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

local notation "projected" => LiveOut.exitInterface (numberedInterface context exits external) fields

variable (a : Lowered (numberedInterface context exits external) fields code)

/-- Exact elaboration and typing of the actual opt-in compiler result. -/
structure Admission (a : Lowered (numberedInterface context exits external) fields code) where
  versioned : SSA P (LiveOut.exitInterface (numberedInterface context exits external) fields).version
  compiled : versioned.source =
    CFG.Cyclic.Versioning.compilePacketLocal (withLiveOut (P := P) fields a.source)

local notation "A" => Region.packedInputType context.toList
local notation "B" => Region.packedExitType (List.ofFn (Interface.external projected))

/-- Use the existing packed dispatcher for the admitted lexical table. -/
def Admission.program (admission : Admission a) : Program P.Instr A B :=
  Program.ofCFGEntry admission.versioned.table.typed

/-- Derive admission from the original source checks at the opt-in numbering.
The actual scoped compiler result is taken from its elaboration. -/
def admit [DecidableEq κ] (R : Fin blocks → Ty κ) (checked : Straight.packetLocalChecks a R = true) :
    Admission a :=
  let graph := CFG.Cyclic.Versioning.compilePacketLocal (withLiveOut (P := P) fields a.source)
  let read := NamedFlat.elaborate graph exits (fun i : Fin n => ((⟨i.val⟩ : Register), 0))
  have success := Straight.compiled_success_packetLocal a R checked
  have found : read.isSome := Option.isSome_iff_exists.mpr (success.imp fun _ h => h.1)
  let table := read.get found
  have typed : table.HasType context (Straight.packetLocalProfile a R) (Interface.external projected) := by
    obtain ⟨target, eq, entry, rows⟩ := success
    have witness : target.HasType context (Straight.packetLocalProfile a R) (Interface.external projected) :=
      ⟨NamedFlat.checkBody_sound _ _ _ entry, fun i => NamedFlat.checkBody_sound _ _ _ (rows i)⟩
    simpa only [table, Option.get_of_eq_some found (show read = some target from eq)] using witness
  ⟨SSA.ofElaborated graph (Option.some_get found).symm typed, rfl⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
