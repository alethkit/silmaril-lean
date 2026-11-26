module

import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize.Thms

/-! # A named request changes its loop packet before taking an ordered exit -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests

open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree vis vis_bind iterate_fixpoint HasTrace out_ret hasTrace_vis_exchange_iff)
open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (ReplyEnumeration ConfigurationEnumeration)

private inductive Op where | poll
  deriving DecidableEq

private inductive Reg : Type 1 where
  | seed | arg | alt | again | rest | left | tail | right | impossible
  deriving DecidableEq

private inductive Label : Type 1 where
  | loop | left | right | first | second
  deriving DecidableEq

private abbrev Bit := Recognize.Bit
private abbrev Packets := Recognize.Packets
private abbrev Replies := Packets

attribute [local instance] Recognize.requestTypes

private abbrev nativeSig := Recognize.signature Op

private abbrev SortName := ULift.{1} Empty
private abbrev bit : Ty SortName := .coprod .unit .unit
private instance : HasTy Op (Ty SortName) :=
  ⟨fun _ => bit, fun _ => LambdaSSA.Region.packedExitType [bit, .unit, .unit]⟩
private instance : HasEff Op Bool := ⟨fun _ => true⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName := { Instr := Op }
private instance : DecidableEq signature.Instr := inferInstanceAs (DecidableEq Op)

private def labels : Fin 5 ≃ Label where
  toFun i := if i = 0 then .loop else if i = 1 then .left else if i = 2 then .right
    else if i = 3 then .first else .second
  invFun
    | .loop => 0
    | .left => 1
    | .right => 2
    | .first => 3
    | .second => 4
  left_inv := by decide +kernel
  right_inv := by intro label; cases label <;> rfl

private def ports : Interface SortName Reg Label := Recognize.interface .seed labels

private def fields (_ : Label) : List (Reg × Ty SortName) := []
private def loopReg (alternate : Bool) : Reg := if alternate then .alt else .arg

/-- The final arm is required by the named sum syntax. Its empty payload
can never be supplied by the shared typed request. -/
private def source (alternate : Bool) (misroute : Bool := false) : CFG Reg Label signature.Instr :=
  let param := loopReg alternate
  ⟨.term (.br .loop (.var .seed)),
    [(.loop, ⟨param, .term (.case (.app .poll (.var param))
      .again (.br .loop (.var .again))
      .rest (.case (.val (.var .rest))
        .left (.br (if misroute then .right else .left) (.var .left))
        .tail (.case (.val (.var .tail))
          .right (.br .right (.var .right)) .impossible (.br .right .unit))))⟩),
     (.left, ⟨.arg, .term (.br .first .unit)⟩),
     (.right, ⟨.arg, .term (.br .second .unit)⟩)]⟩

private def arguments (i : Fin 3) : Ty SortName := if i = 0 then bit else .unit
private def admitNamed (alternate : Bool) (misroute : Bool := false) :=
  PacketLocal.admit (P := signature) ports fields (source alternate misroute) arguments

private def admitted (alternate : Bool) (misroute : Bool := false) :
    Admission signature ports fields (source alternate misroute) :=
  (admitNamed alternate misroute).get (by cases alternate <;> cases misroute <;> decide +kernel)

private abbrev native := Recognize.guardedTable Op.poll

private def leftBit : Syntax.Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def rightBit : Syntax.Payload Bit := ⟨.inr .unit, .inr .unit⟩
private def unitPacket : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

private inductive Event : Type → Type where
  | poll (arg : Bool) : Event (Packet Replies)

private abbrev Runtime := ULift.{1} Unit

universe u

private def isRight {A : Type u} : Value A → Bool
  | .inr _ => true
  | _ => false

private def query : Query nativeSig Event :=
  fun _ p => vis (.poll (isRight p.val)) fun reply => pure ⟨reply⟩

private def raw : Primitive Event signature.Instr Runtime :=
  fun _ x => vis (.poll (isRight x)) fun reply => pure (Recognize.replyValue ULift.up reply)

private def input (x : Syntax.Payload Bit) : Reg × Nat → Value Runtime :=
  fun reg => if reg = (.seed, 0) then Recognize.encodeValue ULift.up x.val else .unit

-- The compiled entry really sends the extra unit field. The native entry
-- forwards its caller directly, so this is an encoding equation.
example : (admitted false).versioned.table.code.entry =
    .br ⟨0, by decide +kernel⟩ (.pair (.bv ⟨0, by decide⟩) .unit) := rfl

-- The named compiler installs a leading product decoder before the query.
example : (admitted false).versioned.table.code.block ⟨0, by decide +kernel⟩ =
    .let₂ (.bv 0) (.case (.op .poll (.bv 1))
      (.br ⟨0, by decide +kernel⟩ (.pair (.bv 0) .unit))
      (.case (.bv 0)
        (.br ⟨1, by decide +kernel⟩ (.pair (.bv 0) .unit))
        (.case (.bv 0)
          (.br ⟨2, by decide +kernel⟩ (.pair (.bv 0) .unit))
          (.br ⟨2, by decide +kernel⟩ (.pair .unit .unit))))) := rfl

private theorem agrees : Recognize.QueryAgreement (P := signature) .poll ULift.up query raw := by
  intro argument
  have key : isRight (Recognize.encodeValue ULift.up argument.val : Value Runtime) = isRight argument.val := by
    cases argument.val <;> rfl
  simp only [raw, query, key, vis_bind, pure_bind]

private def adapter (alternate : Bool) (caller : Syntax.Payload Bit) (misroute : Bool := false) :=
  Recognize.recognizeAdapter (seed := Reg.seed) (names := labels) (admitted alternate misroute)
    .poll ULift.up query raw (input caller) agrees caller rfl

private theorem recognized (alternate : Bool) :
    (Recognize.recognize (seed := Reg.seed) (names := labels) (admitted alternate) .poll).isSome = true := by
  cases alternate <;> decide +kernel

private def correspondence (alternate : Bool) (caller : Syntax.Payload Bit) :
    Corresponds (admitted alternate) native caller query raw (input caller) :=
  (adapter alternate caller).get (by
    simpa only [adapter, Recognize.recognizeAdapter, Option.isSome_map] using recognized alternate)

-- Tag one still carries unit, so the changed named graph passes ordinary
-- typed admission. Its branch now selects the other ordered exit row.
example : (admitNamed false true).isSome = true := by decide +kernel

example : (adapter false leftBit true).isNone = true := by decide +kernel

private def packets : List (Packet Packets) :=
  [⟨0, leftBit⟩, ⟨0, rightBit⟩, ⟨1, unitPacket⟩, ⟨2, unitPacket⟩]

private theorem packets_complete (packet : Packet Packets) : packet ∈ packets := by
  obtain ⟨i, value, typed⟩ := packet
  fin_cases i
  · cases typed with
    | inl typed => cases typed; exact List.Mem.head _
    | inr typed => cases typed; exact List.Mem.tail _ (List.Mem.head _)
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private def replies : ReplyEnumeration nativeSig := ⟨fun _ => packets, fun _ => packets_complete⟩
private def inventory : ConfigurationEnumeration Packets := ⟨packets, packets_complete⟩
private def diagonal : List (Packet Packets × Packet Packets) := packets.map fun p => (p, p)

private noncomputable def observation (alternate : Bool) :=
  LiveOut.observeRaw raw ports.exits (fun k => (fields k).map Prod.fst) (source alternate)
    (fun reg => input leftBit (reg, 0))

example : observation false = observation true :=
  observe_eq_of_checkProduct (correspondence false leftBit) (correspondence true leftBit)
    replies diagonal (by decide +kernel) (fun _ => rfl)

example : (match native.searchProduct native leftBit leftBit replies inventory inventory with
    | .accepted _ => true
    | .mismatch .. => false) = true := by decide +kernel

example : observation false = observation true := by
  obtain ⟨pairs, accepted⟩ := (native.searchProduct_accepts_iff native leftBit leftBit replies inventory
    inventory).mpr ⟨diagonal, by decide +kernel⟩
  exact observe_eq_of_searchProduct (correspondence false leftBit) (correspondence true leftBit)
    replies inventory inventory pairs accepted (fun _ => rfl)

private def runStep := step native leftBit query (unitExit (α := Runtime))

private theorem runsPoll (x : Syntax.Payload Bit) :
    iter runStep (atBlock ⟨0, x⟩) =
      vis (.poll (isRight x.val)) (fun reply => iter runStep (atBlock reply)) := by
  rw [congrFun (iterate_fixpoint runStep) (atBlock ⟨0, x⟩)]
  change ((query .poll x >>= fun p => pure (Sum.inr (atBlock p.down) : Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  simp only [query, vis_bind, pure_bind, Sum.elim_inr]

private theorem runsRight :
    iter runStep (atBlock ⟨2, unitPacket⟩) = pure (unitExit 1) := by
  rw [congrFun (iterate_fixpoint runStep) (atBlock ⟨2, unitPacket⟩)]
  change ((pure (.inr (atExit (R := Packets) 1)) : Tree Event (Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  rw [pure_bind]
  change iter runStep (atExit 1) = _
  rw [congrFun (iterate_fixpoint runStep) (atExit 1)]
  change ((pure (.inl (unitExit 1)) : Tree Event (Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  rw [pure_bind]
  rfl

-- Reply tag zero changes the loop argument from left to right. Reply tag
-- two then leaves at the second ordered exit.
example : HasTrace (observation false)
    (.exchange (.poll false) ⟨0, rightBit⟩
      (.exchange (.poll true) ⟨2, unitPacket⟩ (.result (unitExit 1)))) := by
  unfold observation
  rw [(correspondence false leftBit).observe_eq]
  change HasTrace (iter runStep (atBlock ⟨0, leftBit⟩)) _
  rw [runsPoll]
  apply (hasTrace_vis_exchange_iff _ _ _ _).mpr
  rw [runsPoll]
  apply (hasTrace_vis_exchange_iff _ _ _ _).mpr
  rw [runsRight]
  exact out_ret _

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests
