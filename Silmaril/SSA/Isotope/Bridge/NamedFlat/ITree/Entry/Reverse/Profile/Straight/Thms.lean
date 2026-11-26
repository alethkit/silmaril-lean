module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Straight.Table

/-! # Admission of reverse lowering with zero or one saved capture -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "exitTypes" => Interface.external
  (LiveOut.exitInterface (numberedInterface context exits external) fields)

/-- In a closed entry interface, every saved field of a checked fresh
lowering would have to name a slot in the empty capture context. -/
theorem empty_of_no_captures (closed : n = 0) (saved : a.SavesCaptures) :
    ∀ i, a.savedRegisters i = [] :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.empty_of_no_captures a closed saved

variable [DecidableEq κ]

/-- Source-local checks suffice for successful scoped readback of the actual
versioned program and all its typing checks. The profile is the one computed
by the numbered reverse lowerer. Internal edges can revisit any block. -/
theorem compiled_success (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true) :
    ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.compiled_success a R saved empty checked

/-- Source-local readback and typing for one common saved entry field.
The compiled slots identify the field at every destination, and the attached
source leaves that register alone in every body. Its type comes from the
selected position in the original capture context. -/
theorem compiled_success_capture (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slot : Fin n) (layout : ∀ i, a.savedRegisters i = [⟨slot.val⟩])
    (kept : keepsEntryCapture a slot = true) (checked : checks a R = true) :
    ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.compiled_success_capture
    a R saved slot layout kept checked

private def admitFromReadback (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (success : ∃ table, NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register)) = some table ∧
      let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
      checkBody new context table.entry = true ∧
        ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  let read := NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register))
  have found : read.isSome := Option.isSome_iff_exists.mpr (success.imp fun _ h => h.1)
  let table := read.get found
  let new := SSA.FiniteSum.append (a.packetProfile R saved) exitTypes
  have typed : checkBody new context table.entry = true ∧
      ∀ i, checkBody new (.snoc context (a.packetProfile R saved i)) (table.block i) = true := by
    obtain ⟨_, eq, checks⟩ := success
    simpa only [table, read, Option.get_of_eq_some found eq] using checks
  a.admitOfChecks R saved (Option.some_get found).symm typed.1 typed.2

/-- Admit the actual scoped compiler result using the derived checks. -/
def admit (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  admitFromReadback a R saved (compiled_success a R saved empty checked)

/-- Admit a capture-carrying table at the original entry and exit interface. -/
def admitWithCapture (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (slot : Fin n) (layout : ∀ i, a.savedRegisters i = [⟨slot.val⟩])
    (kept : keepsEntryCapture a slot = true) (checked : checks a R = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  admitFromReadback a R saved (compiled_success_capture a R saved slot layout kept checked)

section Values

open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)

variable [AtomValues κ]

local notation "C" => AtomValues.carrier (κ := κ)
local notation "Input" => Ty.denote C (Region.packedInputType context.toList)

omit [DecidableEq κ] in
/-- The version-zero capture is the same tagged field of the supplied
typed entry record as in the mutable store. -/
theorem capture_at_version_zero (slot : Fin n) (x : Input) :
    store (fun i : Fin n => ((⟨i.val⟩ : Register), 0)) context x (⟨slot.val⟩, 0) =
      inputEnv context x slot.val :=
  (store_version_zero (fun i : Fin n => (⟨i.val⟩ : Register)) context x ⟨slot.val⟩).trans
    (store_at _ (fun _ _ eq => Fin.ext (congrArg ULift.down eq)) context x slot)

omit [DecidableEq κ] in
/-- For a transfer whose saved register still holds the entry field, the
actual versioner's packet contains that tagged field after the argument. -/
theorem encode_capture {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr)
    (slot : Fin n) (x : Input) (transfer : CFG.Cyclic.Transfer Register K (Value (Sigma C)))
    (route : CFG.Cyclic.Versioning.destinations attached transfer.1 = some [⟨slot.val⟩])
    (agrees : transfer.2.2 ⟨slot.val⟩ = inputEnv context x slot.val) :
    CFG.Cyclic.Versioning.encode (treeModel M.raw) attached transfer =
      (transfer.1, .pair transfer.2.1 (.pair (inputEnv context x slot.val) .unit)) := by
  simp [CFG.Cyclic.Versioning.encode, Version.enc, route, Version.packVal, agrees, treeModel]

end Values

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
