module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Defs

/-! # Exact recognition of a constructor-bit request loop -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize

open Silmaril.Elgot.ITree (Tree)
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (FiniteCFG Flat Region)
open LambdaSSA.Semantics.Interaction (Primitive)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet pack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table Row)

abbrev Bit : Syntax.Ty := .coprod .unit .unit
abbrev Packets : List Syntax.Ty := [Bit, .unit, .unit]

/-- Every recognized request consumes a constructor bit. Reply position zero
carries a new bit, and positions one and two carry unit. -/
abbrev requestTypes (Φ : Type) : HasTy Φ Syntax.Ty :=
  ⟨fun _ => Bit, fun _ => Region.packedExitType Packets⟩

attribute [local instance] requestTypes

abbrev signature (Φ : Type) : RequestSignature Φ :=
  ⟨fun _ => Packets, fun _ => rfl⟩

/-- The ordinary guarded table associated with this exact row shape. -/
abbrev guardedTable {Φ : Type} (opcode : Φ) : Table (signature Φ) Packets where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row (signature Φ) Packets [Packets.get i, Bit])
    (.request opcode (.var 0) id (fun _ => rfl))
    (Fin.cases (motive := fun i : Fin 2 => Row (signature Φ) Packets [Packets.get i.succ, Bit])
      (.exit 0) (fun _ => .exit 1))
  selected := fun _ => false

/-- Literal lexical readback of the argument-plus-unit entry, the request
with three replies, and its two unit exit rows. The empty reply tail has
a written branch to row two. -/
def expected {Φ : Type} (opcode : Φ) : FiniteCFG Φ 3 2 1 :=
  ⟨.br 0 (.pair (.bv 0) .unit), Fin.cases (motive := fun _ : Fin 3 => Flat Φ 5 2)
    (.let₂ (.bv 0) (.case (.op opcode (.bv 1))
      (.br 0 (.pair (.bv 0) .unit))
      (.case (.bv 0)
        (.br 1 (.pair (.bv 0) .unit))
        (.case (.bv 0) (.br 2 (.pair (.bv 0) .unit)) (.br 2 (.pair .unit .unit))))))
    (Fin.cases (motive := fun _ : Fin 2 => Flat Φ 5 2)
      (.let₂ (.bv 0) (.br 3 (.pair .unit .unit)))
      (fun _ => .let₂ (.bv 0) (.br 4 (.pair .unit .unit))))⟩

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {E : Type → Type}

/-- The five names are the three written blocks followed by the two exits.
The caller provides one bit at the supplied register name. -/
abbrev interface (seed : V) (names : Fin 5 ≃ K) : Interface κ V K :=
  ⟨1, .snoc .nil (.coprod .unit .unit), fun _ => seed, fun _ _ _ => Subsingleton.elim _ _,
    [names 3, names 4], fun _ => .unit⟩

variable {seed : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}

local notation "I" => (interface (κ := κ) seed names)

variable (a : Admission P (interface (κ := κ) seed names) (fun _ => []) source)

local notation "lexical" => a.versioned.source

/-- Success certifies the exact admitted lexical readback and the first-match
numbering of all five labels. Both checks are independent of reachable rank. -/
structure Checked (opcode : P.Instr) : Type where
  count : (lexical).blocks.length = 3
  accepted : elaborateAt lexical (I).exits (I).version.names 3 count = some (expected opcode)
  numbered : ∀ i : Fin 5, (labelIndex (lexical).blocks (I).exits (names i)).map Fin.val = some i.val

/-- Transport literal readback across the checked written row count. -/
theorem recover_readback {source : CFG V K P.Instr} {d n : Nat} {exits : List K}
    {captures : Fin n → V} {code : FiniteCFG P.Instr d exits.length n}
    (count : source.blocks.length = d) {e : Nat} (changeCount : d = e)
    (read : elaborateAt source exits captures d count = some code) :
    elaborateAt source exits captures e (count.trans changeCount) =
      some (cast (congrArg (fun x => FiniteCFG P.Instr x exits.length n) changeCount) code) := by
  cases changeCount
  exact read

/-- Compare the existing admitted code with the exact entry and row shapes,
then check its named label numbering. No row proof is supplied by the caller. -/
def recognize [DecidableEq P.Instr] (opcode : P.Instr) : Option (Checked a opcode) :=
  if h : a.versioned.table.blocks = 3 then
    let code : FiniteCFG P.Instr 3 2 1 :=
      cast (congrArg (fun x => FiniteCFG P.Instr x 2 1) h) a.versioned.table.code
    let want := expected opcode
    if rows : code.entry = want.entry ∧ ∀ i, code.block i = want.block i then
      have same : code = want := congrArg₂ FiniteCFG.mk rows.1 (funext rows.2)
      let count := a.versioned.count.trans h
      if numbered : (List.finRange 5).all (fun i =>
          decide ((labelIndex (lexical).blocks (I).exits (names i)).map Fin.val = some i.val)) = true then
        some ⟨count, (recover_readback a.versioned.count h a.versioned.accepted).trans
          (congrArg some same),
          fun i => of_decide_eq_true (List.all_eq_true.mp numbered i (List.mem_finRange i))⟩
      else none
    else none
  else none

/-- Re-encode constructor values in the named runtime. The atom arm completes
the function on raw values. No typed packet in this fragment can take it. -/
def encodeValue (atom : Unit → α) : Value Unit → Value α
  | .atom a => .atom (atom a)
  | .unit => .unit
  | .pair a b => .pair (encodeValue atom a) (encodeValue atom b)
  | .inl a => .inl (encodeValue atom a)
  | .inr a => .inr (encodeValue atom a)

/-- Pack the typed reply using the guarded native signature's existing codec. -/
def replyValue (atom : Unit → α) (reply : Packet Packets) : Value α :=
  encodeValue atom (pack reply).val

def encodeCursor (names : Fin 5 ≃ K) (atom : Unit → α) (c : Cursor Packets) : K × Value α :=
  match c.down with
  | .inl i => (names (i.natAdd 3), .pair .unit .unit)
  | .inr p => (names (p.1.castAdd 2), .pair (encodeValue atom p.2.val) .unit)

/-- The shared query evaluator returns the same tagged replies as the raw
named primitive at every typed bit argument. -/
def QueryAgreement (opcode : P.Instr) (atom : Unit → α) (query : Query (signature P.Instr) E)
    (instr : Primitive E P.Instr α) : Prop :=
  ∀ x : Syntax.Payload Bit,
    instr opcode (encodeValue atom x.val) =
      (query opcode x >>= fun p => pure (replyValue atom p.down))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize
