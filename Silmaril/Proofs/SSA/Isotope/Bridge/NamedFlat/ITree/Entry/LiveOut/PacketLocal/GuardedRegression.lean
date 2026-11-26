module

import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Thms

/-! # A named request changes its loop packet before taking an ordered exit -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests

open Silmaril.Elgot (iter liftPure mapReturn)
open Silmaril.Elgot.ITree (Tree vis vis_bind iterate_fixpoint HasTrace out_ret hasTrace_vis_exchange_iff)
open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet pack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table Row ReplyEnumeration ConfigurationEnumeration)

private inductive Op where | poll
  deriving DecidableEq

private inductive Reg : Type 1 where
  | seed | arg | alt | again | rest | left | tail | right | impossible
  deriving DecidableEq

private inductive Label : Type 1 where
  | loop | left | right | first | second
  deriving DecidableEq

private abbrev Bit : Syntax.Ty := .coprod .unit .unit
private abbrev Replies : List Syntax.Ty := [Bit, .unit, .unit]
private abbrev Packets : List Syntax.Ty := [Bit, .unit, .unit]

private instance : HasTy Op Syntax.Ty := ⟨fun _ => Bit, fun _ => LambdaSSA.Region.packedExitType Replies⟩
private def nativeSig : RequestSignature Op := ⟨fun _ => Replies, fun _ => rfl⟩

private abbrev SortName := ULift.{1} Empty
private abbrev bit : Ty SortName := .coprod .unit .unit
private instance : HasTy Op (Ty SortName) :=
  ⟨fun _ => bit, fun _ => LambdaSSA.Region.packedExitType [bit, .unit, .unit]⟩
private instance : HasEff Op Bool := ⟨fun _ => true⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName := { Instr := Op }
private instance : DecidableEq signature.Instr := inferInstanceAs (DecidableEq Op)
private instance : HasTy signature.Instr Syntax.Ty := inferInstanceAs (HasTy Op Syntax.Ty)

private def ports : Interface SortName Reg Label :=
  ⟨1, .snoc .nil bit, fun _ => .seed, fun _ _ _ => Subsingleton.elim _ _, [.first, .second], fun _ => .unit⟩

private def fields (_ : Label) : List (Reg × Ty SortName) := []
private def loopReg (alternate : Bool) : Reg := if alternate then .alt else .arg

/-- The final arm is required by the named sum syntax. Its empty payload
can never be supplied by the shared typed request. -/
private def source (alternate : Bool) : CFG Reg Label signature.Instr :=
  let param := loopReg alternate
  ⟨.term (.br .loop (.var .seed)),
    [(.loop, ⟨param, .term (.case (.app .poll (.var param))
      .again (.br .loop (.var .again))
      .rest (.case (.val (.var .rest))
        .left (.br .left (.var .left))
        .tail (.case (.val (.var .tail))
          .right (.br .right (.var .right)) .impossible (.br .right .unit))))⟩),
     (.left, ⟨.arg, .term (.br .first .unit)⟩),
     (.right, ⟨.arg, .term (.br .second .unit)⟩)]⟩

private def arguments (i : Fin 3) : Ty SortName := if i = 0 then bit else .unit
private def check (alternate : Bool) :=
  PacketLocal.admit (P := signature) ports fields (source alternate) arguments

private def admitted (alternate : Bool) : Admission signature ports fields (source alternate) :=
  (check alternate).get (by cases alternate <;> decide +kernel)

private def native : Table nativeSig Packets where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row nativeSig Packets [Packets.get i, Bit])
    (.request .poll (.var 0) id (fun _ => rfl))
    (Fin.cases (motive := fun i : Fin 2 => Row nativeSig Packets [Packets.get i.succ, Bit])
      (.exit 0) (fun _ => .exit 1))
  selected := fun _ => false

private def leftBit : Syntax.Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def rightBit : Syntax.Payload Bit := ⟨.inr .unit, .inr .unit⟩
private def unitPacket : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

private inductive Event : Type → Type where
  | poll (arg : Bool) : Event (Packet Replies)

private abbrev Runtime := ULift.{1} Unit

private def constructors : Value Unit → Value Runtime
  | .unit => .unit
  | .inl a => .inl (constructors a)
  | .inr a => .inr (constructors a)
  | .pair a b => .pair (constructors a) (constructors b)
  | .atom a => .atom ⟨a⟩

universe u

private def isRight {A : Type u} : Value A → Bool
  | .inr _ => true
  | _ => false

private def query : Query nativeSig Event :=
  fun _ p => vis (.poll (isRight p.val)) fun reply => pure ⟨reply⟩

private def raw : Primitive Event signature.Instr Runtime :=
  fun _ x => vis (.poll (isRight x)) fun reply => pure (constructors (pack reply).val)

private def input (x : Syntax.Payload Bit) : Reg × Nat → Value Runtime :=
  fun reg => if reg = (.seed, 0) then constructors x.val else .unit

private def blockName (i : Fin Packets.length) : Label :=
  Fin.cases .loop (Fin.cases .left (fun _ => .right)) i

private def exitName (i : TwoRequest.Tag) : Label :=
  Fin.cases .first (fun _ => .second) i

private def encode (c : Cursor Packets) : Label × Value Runtime :=
  match c.down with
  | .inl i => (exitName i, .pair .unit .unit)
  | .inr p => (blockName p.1, .pair (constructors p.2.val) .unit)

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

private def namedStep (alternate : Bool) (caller : Syntax.Payload Bit) :=
  CFG.Cyclic.stepSSA (treeModel raw) (admitted alternate).versioned.source.blocks (input caller)

private theorem loopStep (alternate : Bool) (caller packet : Syntax.Payload Bit) :
    namedStep alternate caller (encode (atBlock ⟨0, packet⟩)) =
      vis (.poll (isRight packet.val)) (fun reply => pure (.inr (encode (atBlock reply)))) := by
  cases alternate <;>
    change (Sum.inr <$> ((pure (.pair (constructors packet.val) .unit) >>= (treeModel raw).unpair) >>= _)) = _
  all_goals
    rw [pure_bind]
    change (Sum.inr <$> (pure (constructors packet.val, Value.unit) >>= _)) = _
    rw [pure_bind]
    change (Sum.inr <$> ((raw .poll (constructors packet.val) >>= (treeModel raw).split) >>= _)) = _
    have key : isRight (constructors packet.val) = isRight packet.val := by cases packet.val <;> rfl
    simp only [raw, key, map_eq_pure_bind, vis_bind, pure_bind]
    congr 1
    funext reply
    obtain ⟨i, payload⟩ := reply
    fin_cases i
    · erw [pure_bind, pure_bind]
      rfl
    · change (((treeModel raw).split (.inr (.inl (constructors payload.val))) >>= _) >>= _) = _
      rw [show (treeModel raw).split (.inr (.inl (constructors payload.val))) =
        pure (.inr (.inl (constructors payload.val))) from rfl, pure_bind]
      change (((pure (.inl (constructors payload.val)) >>= (treeModel raw).split) >>= _) >>= _) = _
      rw [pure_bind]
      change ((pure (Sum.inl (constructors payload.val)) >>= _) >>= _) = _
      rw [pure_bind]
      erw [pure_bind]
      rfl
    · change (((treeModel raw).split (.inr (.inr (.inl (constructors payload.val)))) >>= _) >>= _) = _
      rw [show (treeModel raw).split (.inr (.inr (.inl (constructors payload.val)))) =
        pure (.inr (.inr (.inl (constructors payload.val)))) from rfl, pure_bind]
      change (((pure (.inr (.inl (constructors payload.val))) >>= (treeModel raw).split) >>= _) >>= _) = _
      rw [pure_bind]
      change ((pure (Sum.inr (Value.inl (constructors payload.val))) >>= _) >>= _) = _
      rw [pure_bind]
      change (((pure (.inl (constructors payload.val)) >>= (treeModel raw).split) >>= _) >>= _) = _
      rw [pure_bind]
      change ((pure (Sum.inl (constructors payload.val)) >>= _) >>= _) = _
      rw [pure_bind]
      erw [pure_bind]
      rfl

private theorem exitRowStep (alternate : Bool) (caller : Syntax.Payload Bit)
    (tag : TwoRequest.Tag) (payload : Value Runtime) :
    namedStep alternate caller (blockName tag.succ, .pair payload .unit) =
      pure (.inr (encode (atExit tag))) := by
  fin_cases tag <;> cases alternate <;>
    change (Sum.inr <$> ((pure (.pair payload .unit) >>= (treeModel raw).unpair) >>= _)) = _
  all_goals
    rw [pure_bind]
    change (Sum.inr <$> (pure (payload, Value.unit) >>= _)) = _
    rw [pure_bind]
    change (Sum.inr <$> (pure _ : Tree Event (Label × Value Runtime))) = _
    rw [map_pure]
    rfl

private def number (p : Label × Value Runtime) : Transfer Runtime :=
  FiniteCFG.packedTreeOutput (treeExitNumber ports.exits p)

private theorem localStep (alternate : Bool) (caller : Syntax.Payload Bit) (c : Cursor Packets) :
    (step native caller query unitExit c >>= liftPure (Sum.map id encode)) =
      mapReturn (namedStep alternate caller) (liftPure number) (encode c) := by
  rcases c with ⟨tag | ⟨i, payload⟩⟩
  · have miss : namedStep alternate caller (encode (atExit tag)) = pure (.inl (encode (atExit tag))) := by
      fin_cases tag <;> cases alternate <;> rfl
    change (pure (.inl (unitExit tag : Transfer Runtime)) >>= liftPure (Sum.map id encode)) =
      mapReturn (namedStep alternate caller) (liftPure number) (encode (atExit tag))
    unfold mapReturn
    rw [miss, pure_bind, pure_bind]
    fin_cases tag <;> simp [liftPure, unitExit, number, encode, atExit, exitName, ports, treeExitNumber,
      treeNumber] <;> rfl
  · fin_cases i
    · change ((query .poll payload >>= fun reply => pure (.inr (atBlock reply.down))) >>=
          liftPure (Sum.map id encode)) =
        mapReturn (namedStep alternate caller) (liftPure number) (encode (atBlock ⟨0, payload⟩))
      unfold mapReturn
      rw [loopStep]
      simp only [query, vis_bind, liftPure, Function.comp_apply, pure_bind, Sum.elim_inr, Sum.map_inr]
    · change (pure (Sum.inr (atExit (R := Packets) 0) : Transfer Runtime ⊕ Cursor Packets) >>=
          liftPure (Sum.map id encode)) =
        mapReturn (namedStep alternate caller) (liftPure number)
          (blockName (Fin.succ (0 : TwoRequest.Tag)), .pair (constructors payload.val) .unit)
      unfold mapReturn
      rw [exitRowStep, pure_bind, pure_bind]
      rfl
    · change (pure (Sum.inr (atExit (R := Packets) 1) : Transfer Runtime ⊕ Cursor Packets) >>=
          liftPure (Sum.map id encode)) =
        mapReturn (namedStep alternate caller) (liftPure number)
          (blockName (Fin.succ (1 : TwoRequest.Tag)), .pair (constructors payload.val) .unit)
      unfold mapReturn
      rw [exitRowStep, pure_bind, pure_bind]
      rfl

private def correspondence (alternate : Bool) (caller : Syntax.Payload Bit) :
    Corresponds (admitted alternate) native caller query raw (input caller) where
  encode := encode
  entry := by cases alternate <;> rfl
  localStep := localStep alternate caller

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
