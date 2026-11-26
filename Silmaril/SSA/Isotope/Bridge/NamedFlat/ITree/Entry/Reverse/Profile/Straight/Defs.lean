module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Defs

/-! # Source-local checks for reversion -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

/-- Recognize the straight-line subset, with a jump as the final terminator. -/
def bodySupported {V K : Type u} {F : Type v} : CFG.Body V K F → Bool
  | .let1 _ _ tail | .let2 _ _ _ tail => bodySupported tail
  | .term (.br ..) => true
  | .term (.case ..) => false

variable {Base V K : Type u} {F : Type v} {n labels : Nat}
  [DecidableEq V] [DecidableEq Base] [HasTy F (Ty Base)]

/-- Check an unversioned body in its original argument and capture context.
The named terminator grammar supports jumps and nested sum cases. -/
def sourceCheck (index : K → Option (Fin labels)) (types : Fin labels → Ty Base)
    (names : Names V n) (ctx : BoundCtx (Ty Base) n) (src : CFG.Body V K F) : Bool :=
  ((NamedFlat.body index names src).map (checkBody types ctx)).getD false

variable {κ K : Type (u + 1)} [DecidableEq K] [DecidableEq κ]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : LambdaSSA.FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "versioned" => Versioning.compile attached
local notation "exitTypes" => Interface.external
  (LiveOut.exitInterface (numberedInterface context exits external) fields)

/-- Check the original entry and every original block with their original
packet types. Use the versioned label order, which retains the written
block order, to avoid a separate numbering in the local checks. -/
def checks (R : Fin blocks → Ty κ) : Bool :=
  let original := fun i => R (Fin.cast a.reversionCount i)
  let types := SSA.FiniteSum.append original exitTypes
  let index := labelIndex (versioned).blocks exits
  sourceCheck index types (first fun i : Fin n => (⟨i.val⟩ : Register)) context (attached).entry &&
    (List.finRange (versioned).blocks.length).all fun i =>
      let b := (attached).blocks[Fin.cast (List.length_map _) i].2
      sourceCheck index types (blockNames b.param) (.snoc context (original i)) b.body

/-- The selected input register has no assignment or case binder in the
attached entry or block bodies. Packet parameters are checked by the actual
saved slot lists. -/
def keepsEntryCapture (slot : Fin n) : Bool :=
  let reg : Register := ⟨slot.val⟩
  decide (reg ∉ (attached).entry.toRegion.bound) &&
    (attached).blocks.all (fun block => decide (reg ∉ block.2.body.toRegion.bound))

/-- The unchanged entry registers and their types in the saved packet order. -/
def captureFields (ctx : BoundCtx (Ty κ) n) (slots : List (Fin n)) : List (Register.{u} × Ty κ) :=
  slots.map fun i => (⟨i.val⟩, ctx.get i)

/-- Check that the selected input slots are unassigned in all attached bodies. -/
def keepsEntryCaptures (slots : List (Fin n)) : Bool :=
  slots.all (keepsEntryCapture a)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
