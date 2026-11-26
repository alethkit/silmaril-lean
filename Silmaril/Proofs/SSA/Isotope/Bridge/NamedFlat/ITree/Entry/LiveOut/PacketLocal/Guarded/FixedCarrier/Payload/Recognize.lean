module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Recognize.Defs
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (iter mapReturn liftPure)
open Silmaril.Elgot.ITree (Tree iterate_fixpoint vis_bind)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Transfer region)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ReplyEnumeration ConfigurationEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head Table)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint exit_type)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit requestTypes interface encodeValue)
open LiveBit (PayloadType rawWithLiterals)

attribute [local instance] requestTypes

theorem decode_return (p : Packet Outputs) :
    LiveBit.decode (packedReturn p) = some (p.1, p.2.val) := by
  rcases p with ⟨tag, value, typed⟩
  fin_cases tag <;>
    cases typed with
    | pair old field =>
      cases old
      cases field with
      | pair bit tail =>
        cases tail
        cases bit with
        | inl bit => cases bit; rfl
        | inr bit => cases bit; rfl

theorem roots {Φ : Type} {A : Syntax.Ty} (g : Endpoint (Recognize.signature Φ) Incoming A)
    (caller : Syntax.Payload (Incoming.get (g).control.entry)) :
    RootAgrees g caller (packetTree g caller) := by
  intro p
  unfold packetTree
  rw [congrFun (iterate_fixpoint (payloadStep g caller))]
  change (payloadStep g caller ⟨.inr p⟩ >>= Sum.elim pure (iter (payloadStep g caller))) = _
  have head : payloadStep g caller ⟨.inr p⟩ =
      (match (g).control.head caller p with
      | .exit i _ => pure (Sum.inr (⟨.inl ((g).returnPacket caller p i)⟩ : Phase A))
      | .diverge => Silmaril.Elgot.ITree.diverge
      | .request f arg next => query f arg >>= fun r =>
        pure (Sum.inr (⟨.inr (next r.down.1 r.down.2)⟩ : Phase A))) := rfl
  rw [head]
  cases (g).control.head caller p with
  | exit i _ =>
    rw [pure_bind, Sum.elim_inr, congrFun (iterate_fixpoint (payloadStep g caller))]
    change (pure (Sum.inl ((packedReturn ((g).returnPacket caller p i)))) >>= _) = _
    simp only [pure_bind, Sum.elim_inl]
    rfl
  | diverge => simp
  | request f x next => simp [query, vis_bind]

private theorem literal_query {Φ : Type} (literals : Φ → Option Bool) (op : Φ) :
    ∀ x : Syntax.Payload Bit, rawWithLiterals literals op (encodeValue ULift.up x.val) =
      (query op x >>= fun p => pure (Recognize.replyValue ULift.up p.down)) := by
  rintro ⟨value, typed⟩
  cases typed with
  | inl h => cases h; exact query_agrees op ⟨.inl .unit, .inl .unit⟩
  | inr h => cases h; exact query_agrees op ⟨.inr .unit, .inr .unit⟩

private theorem cast_val {A B : Syntax.Ty} (h : A = B) (p : Syntax.Payload A) :
    (cast (congrArg Syntax.Payload h) p).val = p.val := by cases h; rfl

theorem request_row_transfer {κ : Type 1} {P : FlatInstitution.Signature.{0, 0} κ}
    {A : Syntax.Ty} (literals : P.Instr → Option Bool) (op : P.Instr)
    (routes : Recognize.TypedRoutes Incoming.get) (bitTag unitTag : Tag) (selected : Tag → Bool)
    (output : (i : Fin 3) → Syntax.Expr [Incoming.get i, Bit] A)
    (caller payload : Syntax.Payload Bit) (env : Env Runtime) :
    region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up payload.val) .unit))
      (Recognize.requestRow op routes.destination).erase =
      rowTransfer ⟨guardedControl routes op bitTag unitTag selected, output⟩ caller ⟨0, payload⟩ := by
  rw [Recognize.eval_request (P := P)
    (opcode := op) ULift.up query (rawWithLiterals literals) _ (literal_query literals op) env payload]
  change _ = (query op payload >>= fun r => (pure ((routes.destination r.down.1).val,
    .pair (encodeValue ULift.up (cast (congrArg Syntax.Payload (routes.packet r.down.1).symm) r.down.2).val) .unit) :
    Tree (Request P.Instr) (Transfer Runtime)))
  congr 1
  funext r
  change ULift.{1} (Packet Recognize.Packets) at r
  exact congrArg (fun v => (pure ((routes.destination r.down.1).val,
    .pair (encodeValue ULift.up v) .unit) : Tree (Request P.Instr) (Transfer Runtime)))
    (cast_val (routes.packet r.down.1).symm r.down.2).symm

private theorem eval_write {Φ : Type} {hasBit : Bool} (literals : Φ → Option Bool)
    (w : Write Φ hasBit) (agree : w.Agrees literals) (tag : Tag) (env : Env Runtime)
    (input : Syntax.Payload (if hasBit then Bit else .unit)) (caller : Syntax.Bindings [Bit]) :
    region (rawWithLiterals literals) (extend env (.pair (encodeValue ULift.up input.val) .unit)) (w.row tag).erase =
      pure (tag.natAdd 3 |>.val, encodeValue ULift.up (w.output.eval (caller.push input)).val) := by
  cases w with
  | read =>
    simp only [Write.row, Write.output, Flat.erase, Morphism.CaseSSA.erase, region,
      LambdaSSA.Semantics.Interaction.term, pure_bind]
    rfl
  | literal op b =>
    have lit : literals op = some b := agree
    cases b <;> simp [Write.row, Write.output, LiveBit.payloadExpr, Recognize.exitRow, Flat.erase,
      Morphism.CaseSSA.erase, region, LambdaSSA.Semantics.Interaction.term, rawWithLiterals,
      lit, extend, Recognize.bitValue, Syntax.Expr.eval] <;> rfl


theorem unfold_return {Φ : Type} {A : Syntax.Ty} (g : Endpoint (Recognize.signature Φ) Incoming A)
    (caller : Syntax.Payload (Incoming.get (g).control.entry)) (p : Packet Incoming) (i : Tag) :
    packetValue ((g).returnPacket caller p i) =
      encodeValue ULift.up ((g.output p.1).eval (((g).control.bindings caller).push p.2)).val :=
  congrArg (encodeValue ULift.up) (cast_val (exit_type i).symm _)

private theorem restore_block {K : Type 1} (names : Fin 5 ≃ K) (i : Fin 3) (p : Value Runtime) :
    Recognize.restore names (i.val, p) = (names (i.castAdd 2), p) := by
  unfold Recognize.restore
  rw [dite_eq_left (show i.val < 5 by omega)]
  rfl

private theorem restore_exit {K : Type 1} (names : Fin 5 ≃ K) (i : Tag) (p : Value Runtime) :
    Recognize.restore names ((i.natAdd 3).val, p) = (names (i.natAdd 3), p) := by
  unfold Recognize.restore
  rw [dite_eq_left (i.natAdd 3).isLt]

section Replay

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr} {fields : K → List (V × Ty κ)}
  {a : Admission P (interface seed names) fields source} {target : FiniteCFG P.Instr 3 2 1}
  {A : Syntax.Ty} {literals : P.Instr → Option Bool}
  (readback : Recognize.Readback a target) (g : Endpoint (Recognize.signature P.Instr) Incoming A)
  (caller : Syntax.Payload (Incoming.get g.control.entry)) (entryBit : Syntax.Payload Bit)
  (store : V → Value Runtime)

local notation "instr" => (rawWithLiterals literals)
local notation "initial" => (fun r : V × Nat => store (Prod.fst r))
local notation "I" => (interface (κ := κ) seed names)
local notation "packed" => (fun p => FiniteCFG.packedTreeOutput (treeExitNumber [names 3, names 4] p))

include readback in
private theorem named_entry (entryShape : target.entry = .br 0 (.pair (.bv 0) .unit))
    (seedValue : store seed = encodeValue ULift.up entryBit.val) :
    a.versioned.source.entry.evalJump (treeModel instr) initial =
      pure (encodePhase (A := A) names ⟨.inr ⟨0, entryBit⟩⟩) := by
  let env : Env Runtime := fun _ => encodeValue ULift.up entryBit.val
  rw [readback.entry_eval instr initial env (fun _ => seedValue.symm)]
  rw [entryShape]
  simp only [ Flat.erase, Morphism.CaseSSA.erase, region,
    LambdaSSA.Semantics.Interaction.term, pure_bind]
  rfl

include readback in
private theorem named_step (row : ∀ (p : Packet Incoming) (env : Env Runtime),
    region instr (extend env (.pair (encodeValue ULift.up p.2.val) .unit)) (target.block p.1).erase =
      rowTransfer g caller p) (phase : Phase A) :
    (payloadStep g caller phase >>= liftPure (Sum.map id (encodePhase names))) =
      mapReturn (CFG.Cyclic.stepSSA (treeModel instr) a.versioned.source.blocks initial) (liftPure packed)
        (encodePhase names phase) := by
  rcases phase with ⟨p | p⟩
  · simp only [payloadStep, pure_bind, liftPure, Function.comp_apply, Sum.map_inl, id_eq]
    exact (readback.exit_eval instr initial (packetValue p) p.1).symm
  · let env : Env Runtime := fun _ => .unit
    change _ = mapReturn (CFG.Cyclic.stepSSA (treeModel instr) a.versioned.source.blocks initial)
      (liftPure packed) (names (p.1.castAdd 2), .pair (encodeValue ULift.up p.2.val) .unit)
    unfold mapReturn
    rw [readback.block_eval instr initial env, row p env, rowTransfer]
    unfold payloadStep
    dsimp only
    cases (g).control.head caller p with
    | exit i _ =>
      simp only [pure_bind, liftPure, Function.comp_apply, Sum.map_inr, Sum.elim_inr, encodePhase, restore_exit]
      rfl
    | diverge =>
      simp only [Silmaril.Elgot.ITree.diverge_bind]
    | request f arg next =>
      simp only [bind_assoc, pure_bind, liftPure, Function.comp_apply, Sum.map_inr, Sum.elim_inr,
        encodePhase, restore_block]

include readback in
theorem named_tree_of_readback
    (entryShape : target.entry = .br 0 (.pair (.bv 0) .unit))
    (seedValue : store seed = encodeValue ULift.up entryBit.val)
    (row : ∀ (p : Packet Incoming) (env : Env Runtime),
      region instr (extend env (.pair (encodeValue ULift.up p.2.val) .unit)) (target.block p.1).erase =
        rowTransfer g caller p) :
    LiveOut.observeRaw instr (I).exits (fun k => (fields k).map Prod.fst) source store =
      packetTree g caller ⟨0, entryBit⟩ := by
  unfold packetTree
  exact Guarded.observe_eq_of_steps (a := a) (input := initial) (⟨.inr ⟨0, entryBit⟩⟩ : Phase A)
    (payloadStep g caller) (encodePhase names) (named_entry readback entryBit store entryShape seedValue)
    (named_step readback g caller store row)

end Replay

section NamedTree

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed reg : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}
  {a : Admission P (interface seed names) (LiveBit.fields reg) source}
  {op : P.Instr} {literals : P.Instr → Option Bool}
  (ck : Checked a op literals) (selected : Tag → Bool) (caller : Syntax.Payload Bit)
  (store : V → Value Runtime)

local notation "g" => (ck.profile.endpoint op selected)
local notation "instr" => (rawWithLiterals literals)
local notation "I" => (interface (κ := κ) seed names)

private theorem eval_block (p : Packet Incoming) (env : Env Runtime) :
    region instr (extend env (.pair (encodeValue ULift.up p.2.val) .unit))
      ((ck.profile.expected op).block p.1).erase =
      rowTransfer g caller p := by
  rcases p with ⟨i, payload⟩
  fin_cases i
  · exact request_row_transfer (P := P) literals op ck.profile.routes ck.profile.bitTag ck.profile.unitTag
      selected (g).output caller payload env
  · change _ = pure ((ck.profile.bitTag.natAdd 3).val, packetValue ((g).returnPacket caller ⟨1, payload⟩ ck.profile.bitTag))
    rw [unfold_return]
    exact eval_write literals ck.profile.fromBit ck.literals_agree.1 _ env payload _
  · change _ = pure ((ck.profile.unitTag.natAdd 3).val, packetValue ((g).returnPacket caller ⟨2, payload⟩ ck.profile.unitTag))
    rw [unfold_return]
    exact eval_write literals ck.profile.fromUnit ck.literals_agree.2 _ env payload _

theorem named_tree (seedValue : store seed = encodeValue ULift.up caller.val) :
    LiveOut.observeRaw instr (I).exits (fun _ => [reg]) source store = packetTree g caller ⟨0, caller⟩ :=
  named_tree_of_readback ck.readback g caller caller store rfl seedValue (eval_block ck selected caller)

end NamedTree

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  {seed reg : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}
  {a : Admission P (interface seed names) (LiveBit.fields reg) source}
  {op : P.Instr} {literals : P.Instr → Option Bool}

local notation "I" => (interface (κ := κ) seed names)

/-- Exact native readback and successful named recognition give the same
decorated observations on the supplied deterministic carrier. -/
theorem observe_native {states results : Nat} [DecidableEq P.Instr] (ck : Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (codec : Fin results ≃ Packet Outputs) (prim : Syntax.Primitives P.Instr states)
    (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states) (s : Fin states) :
    LiveBit.observeNamed source names reg store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s := by
  unfold LiveBit.observeNamed
  change FixedCarrier.decorate prim selected
    (FixedCarrier.observe prim (LiveOut.observeRaw (rawWithLiterals literals) (I).exits (fun _ => [reg])
      source store) s LiveBit.decode) PayloadType = _
  rw [named_tree ck selected caller store seedValue]
  exact observe_roots_native (ck.profile.endpoint op selected) codec caller raw valid prim configs stores
    (packetTree (ck.profile.endpoint op selected) caller) (roots (ck.profile.endpoint op selected) caller)
    LiveBit.decode decode_return s

section Comparison

variable {target : CFG V K P.Instr}
  {b : Admission P (interface seed names) (LiveBit.fields reg) target}
  {op' : P.Instr} [DecidableEq P.Instr] {states results : Nat}
  (l : Checked a op literals) (r : Checked b op' literals)
  (caller caller' : Syntax.Payload Bit) (store store' : V → Value Runtime)
  (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller'.val)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
  (codec : Fin results ≃ Packet Outputs) (replies : ReplyEnumeration (Recognize.signature P.Instr))
  (configs : ConfigurationEnumeration Incoming) (stores : StateInventory states)
  (valid : (l.profile.endpoint op selected).checkNative raw = true)
  (valid' : (r.profile.endpoint op' selected').checkNative raw' = true)

include seedValue seedValue' valid valid'

/-- With both named and native checks accepted, the verdict compares the
original named runners under a shared interpreter and initial machine state. -/
theorem acceptance_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        LiveBit.observeNamed source names reg store literals prim s selected ≤
          LiveBit.observeNamed target names reg store' literals prim s selected' := by
  have left (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native l selected caller store seedValue raw valid codec prim configs stores s
  have right (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native r selected' caller' store' seedValue' raw' valid' codec prim configs stores s
  simpa only [← left, ← right] using!
    (l.profile.endpoint op selected).acceptance_iff (r.profile.endpoint op' selected') raw raw' codec
      caller caller' replies configs configs stores valid valid'

/-- With both readbacks accepted, a negative verdict is exactly a semantic
counterexample on the original named runners. Unsupported syntax gives none. -/
theorem rejection_iff :
    compare? (some l) (some r) raw raw' selected selected' codec caller caller' replies configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ LiveBit.observeNamed source names reg store literals prim s selected ≤
          LiveBit.observeNamed target names reg store' literals prim s selected' := by
  have left (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native l selected caller store seedValue raw valid codec prim configs stores s
  have right (prim : Syntax.Primitives P.Instr states) (s : Fin states) :=
    observe_native r selected' caller' store' seedValue' raw' valid' codec prim configs stores s
  simpa only [← left, ← right] using!
    (l.profile.endpoint op selected).rejection_iff (r.profile.endpoint op' selected') raw raw' codec
      caller caller' replies configs configs stores valid valid'

end Comparison

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.PayloadRecognition
