module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits resultBehaviour)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (ConfigurationEnumeration ReplyEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open Recognize (Bit Packets guardedTable)

attribute [local instance] Recognize.requestTypes

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed : V} {names : Fin 5 ≃ K}
  {source target : CFG V K P.Instr} {states : Nat}
  {a : Admission P (Recognize.interface seed names) (fun _ => []) source}
  {b : Admission P (Recognize.interface seed names) (fun _ => []) target}
  {op op' : P.Instr}

/-- The existing finite classifier computes the observation of the actual
named runner when its typed request replies come from this interpreter. -/
theorem observeNamed_runFinite (checked : Recognize.Checked a op) (caller : Syntax.Payload Bit)
    (input : V → Value Runtime) (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (s : Fin states) :
    observeNamed source names input prim s =
      resultBehaviour ((guardedTable op checked.routes).runFinite caller prim configs stores ⟨0, caller⟩ s) :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.observeNamed_runFinite
    checked caller input value prim configs stores s

/-- Exact lexical recognition and native readback give equal decorated
observations at the same caller bit and machine state. This retains the
ordered exit tag, the final machine state on exits and faults, and divergence. -/
theorem observeNamed_native [DecidableEq P.Instr] (checked : Recognize.Checked a op)
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native : CFG.Dependent.Native.Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op checked.routes).checkNative native = true) (s : Fin states) :
    observeNamed source names input prim s =
      Shape.denote (withExitUB native (guardedTable op checked.routes).selected)
        (Syntax.model prim ((guardedTable op checked.routes).bindings caller)) s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.observeNamed_native
    checked caller input value prim configs stores native readback s

/-- On recognized named endpoints with exact native readback, the existing
decision is equivalent to refinement for every total typed interpreter on
the fixed carrier, at every initial machine state and the supplied caller bit. -/
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
        observeNamed source names input prim s ≤ observeNamed target names input prim s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.acceptance_iff
    left right caller input value replies configs stores native native' readback readback'

/-- With both readbacks checked, a negative verdict has an interpreter and
initial state witnessing failure at the original named endpoints. -/
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
        ¬ observeNamed source names input prim s ≤ observeNamed target names input prim s :=
  Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.rejection_iff
    left right caller input value replies configs stores native native' readback readback'

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
