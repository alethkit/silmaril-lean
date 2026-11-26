module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Straight.Table

/-! # Admission of straight-line reverse lowering with empty saved records -/

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

/-- Admit the actual scoped compiler result using the derived checks. -/
def admit (R : Fin blocks → Ty κ) (saved : a.SavesCaptures)
    (empty : ∀ i, a.savedRegisters i = []) (checked : checks a R = true) :
    LiveOut.Admission P (numberedInterface context exits external) fields a.source :=
  let read := NamedFlat.compile attached exits (fun i : Fin n => (⟨i.val⟩ : Register))
  have found : read.isSome := Option.isSome_iff_exists.mpr
    ((compiled_success a R saved empty checked).imp fun _ h => h.1)
  have typed := Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight.compiled_get_checks
    a R saved empty checked found
  a.admitOfChecks R saved (Option.some_get found).symm typed.1 typed.2

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
