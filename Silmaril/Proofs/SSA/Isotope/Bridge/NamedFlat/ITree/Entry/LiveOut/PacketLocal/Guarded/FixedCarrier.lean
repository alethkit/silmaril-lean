module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Defs
import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open Silmaril
open Silmaril.Isotope
open Silmaril.Elgot (iter)
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (Tree vis ret out out_vis out_ret vis_bind iterate_fixpoint)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Recognize (Bit Packets guardedTable)
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape (denote)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet unpack)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits resultBehaviour)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (Head Table ConfigurationEnumeration ReplyEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier (encode rows)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)

attribute [local instance] Recognize.requestTypes

variable {Φ : Type} {states : Nat}

theorem query_agrees (op : Φ) :
    ∀ arg : Syntax.Payload Bit,
      raw op (Recognize.encodeValue ULift.up arg.val) =
        (query op arg >>= fun p => pure (Recognize.replyValue ULift.up p.down)) := by
  rintro ⟨value, typed⟩
  cases typed with
  | inl typed => cases typed; simp only [raw, query, Recognize.encodeValue, vis_bind, pure_bind]; rfl
  | inr typed => cases typed; simp only [raw, query, Recognize.encodeValue, vis_bind, pure_bind]; rfl

private theorem exitTag_unit (i : Fin 2) : exitTag (unitExit (α := Runtime) i) = some i := by
  fin_cases i <;> rfl

private theorem run_head (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (p : Packet Packets) :
    iter (m := Tree (Request Φ)) (step g caller query (unitExit (α := Runtime))) (atBlock p) =
      match g.head caller p with
      | .exit i _ => ret (unitExit i)
      | .request f arg next =>
        vis (.call f arg) (fun reply =>
          iter (step g caller query (unitExit (α := Runtime))) (atBlock (next reply.1 reply.2))) := by
  rw [congrFun (iterate_fixpoint (step g caller query (unitExit (α := Runtime)))) (atBlock p)]
  change (headStep query (g.head caller p) >>= _) = _
  cases g.head caller p with
  | exit i selected =>
    simp only [headStep, pure_bind, Sum.elim_inr]
    rw [congrFun (iterate_fixpoint (step g caller query (unitExit (α := Runtime)))) (atExit i)]
    simp only [step, atExit, pure_bind, Sum.elim_inl]
    rfl
  | request f arg next =>
    simp only [headStep, query, vis_bind, pure_bind, Sum.elim_inr]

private noncomputable def carrier (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry))
    (configs : ConfigurationEnumeration Packets) (stores : StateInventory states) :
    PositionalCarrier Loop Exits (RunTree Φ) (Fin states) (configs.invocations stores).length 2 states where
  invocation code :=
    let input := (configs.invocations stores).get code
    (0, .atom (iter (m := Tree (Request Φ)) (step g caller query (unitExit (α := Runtime))) (atBlock input.1)), input.2)
  result := ⟨fun i => (i, .unit), fun _ _ eq => congrArg Prod.fst eq⟩
  final := ⟨id, fun _ _ eq => eq⟩

private theorem get_encode (configs : ConfigurationEnumeration Packets) (stores : StateInventory states)
    (p : Packet Packets × Fin states) : (configs.invocations stores).get (encode configs stores p) = p :=
  List.getElem_idxOf _

private theorem step_row (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration Packets) (stores : StateInventory states)
    (code : Fin (configs.invocations stores).length) :
    feedback prim (invocationPoint (carrier g caller configs stores).invocation code) =
      (rows g caller prim configs stores code).routed (carrier g caller configs stores) := by
  let i := (configs.invocations stores).get code
  change treeStep prim
    (iter (m := Tree (Request Φ)) (step g caller query (unitExit (α := Runtime))) (atBlock i.1)) i.2 = _
  rw [run_head, rows]
  dsimp only
  cases h : g.head caller i.1 with
  | exit tag selected =>
    simp [Head.execute, treeStep, exitTag_unit, Row.routed, carrier, terminal]
    rfl
  | request f arg next =>
    simp only [Head.execute, treeStep, out_vis, Part.some_dom, ↓reduceDIte, Part.get_some]
    cases hp : prim f arg i.2 with
    | ret reply t =>
      simp only [Row.routed, carrier]
      rw [get_encode]
      rfl
    | fault t => rfl
    | diverge => rfl

private theorem project_result (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry))
    (configs : ConfigurationEnumeration Packets) (stores : StateInventory states) (r : Result 2 states) :
    (r.routed (carrier g caller configs stores)).map (Set.image project) = resultBehaviour r := by
  cases r <;> simp [Result.routed, carrier, project, resultBehaviour]
  rfl

theorem observe_runFinite (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration Packets) (stores : StateInventory states)
    (ordinary : ∀ i, g.selected i = false) (p : Packet Packets) (s : Fin states) :
    FixedCarrier.observe prim
      (iter (m := Tree (Request Φ)) (step g caller query (unitExit (α := Runtime))) (atBlock p)) s =
      resultBehaviour (g.runFinite caller prim configs stores p s) := by
  have h := classify_routed (f := feedback prim) (carrier g caller configs stores)
    (rows g caller prim configs stores) (encode configs stores (p, s)) (step_row g caller prim configs stores)
  have atStart : invocationPoint (carrier g caller configs stores).invocation
      (encode configs stores (p, s)) =
      .block 0 (.atom (iter (m := Tree (Request Φ)) (step g caller query (unitExit (α := Runtime))) (atBlock p))) s := by
    simp only [invocationPoint, carrier, get_encode]
  rw [atStart] at h
  unfold FixedCarrier.observe Table.runFinite
  rw [h, project_result]
  cases execute (rows g caller prim configs stores) (encode configs stores (p, s)) <;>
    simp [Table.markExit, ordinary]

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed : V} {names : Fin 5 ≃ K}
  {source target : CFG V K P.Instr}
  {a : Admission P (Recognize.interface seed names) (fun _ => []) source}
  {b : Admission P (Recognize.interface seed names) (fun _ => []) target}
  {op op' : P.Instr}

theorem observeNamed_runFinite (checked : Recognize.Checked a op) (caller : Syntax.Payload Bit)
    (input : V → Value Runtime) (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (s : Fin states) :
    observeNamed source names input prim s =
      resultBehaviour ((guardedTable op checked.routes).runFinite caller prim configs stores ⟨0, caller⟩ s) := by
  let c := checked.corresponds ULift.up query raw (fun reg => input reg.1) (query_agrees op) caller value
  exact (congrArg (fun tree => FixedCarrier.observe prim tree s) c.observe_eq).trans
    (observe_runFinite (guardedTable op checked.routes) caller prim configs stores (fun _ => rfl) ⟨0, caller⟩ s)

theorem observeNamed_native [DecidableEq P.Instr] (checked : Recognize.Checked a op)
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native : CFG.Dependent.Native.Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op checked.routes).checkNative native = true) (s : Fin states) :
    observeNamed source names input prim s =
      Shape.denote (withExitUB native (guardedTable op checked.routes).selected)
        (Syntax.model prim ((guardedTable op checked.routes).bindings caller)) s := by
  let g := guardedTable op checked.routes
  calc
    _ = resultBehaviour (g.runFinite caller prim configs stores ⟨0, caller⟩ s) :=
      observeNamed_runFinite checked caller input value prim configs stores s
    _ = g.observeAt caller prim ⟨0, caller⟩ s := (g.observe_runFinite caller prim configs stores _ s).symm
    _ = _ := (g.observe_entry native readback caller prim s).symm

theorem acceptance_iff [DecidableEq P.Instr] (left : Recognize.Checked a op) (right : Recognize.Checked b op')
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : CFG.Dependent.Native.Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true) :
    (guardedTable op left.routes).checkAllInterpreters? (guardedTable op' right.routes) native native'
        caller caller replies configs configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        observeNamed source names input prim s ≤ observeNamed target names input prim s := by
  rw [Table.checkAllInterpreters?_accepts_iff, and_iff_right readback, and_iff_right readback']
  exact forall_congr' fun prim => forall_congr' fun s => by
    rw [observeNamed_native left caller input value prim configs stores native readback s,
      observeNamed_native right caller input value prim configs stores native' readback' s]
    rfl

theorem rejection_iff [DecidableEq P.Instr] (left : Recognize.Checked a op) (right : Recognize.Checked b op')
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : CFG.Dependent.Native.Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true) :
    (guardedTable op left.routes).checkAllInterpreters? (guardedTable op' right.routes) native native'
        caller caller replies configs configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ observeNamed source names input prim s ≤ observeNamed target names input prim s := by
  classical
  have accepted := acceptance_iff left right caller input value replies configs stores native native' readback readback'
  simp only [Table.checkAllInterpreters?, readback, readback', Bool.and_self, ↓reduceIte,
    Option.some.injEq] at accepted ⊢
  simp only [Bool.eq_false_iff, ne_eq, accepted, not_forall]

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
