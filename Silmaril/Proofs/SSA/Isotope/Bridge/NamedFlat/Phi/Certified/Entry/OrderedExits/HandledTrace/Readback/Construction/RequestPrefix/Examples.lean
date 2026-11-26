module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.Examples

open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (region)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Atom Denote PacketType PrimitiveSignature)

private inductive Op where
  | first | second | third
  deriving DecidableEq

private def inputType : PacketType := .product .unit .unit
private def bit : PacketType := .coprod .unit .unit

private def sig : PrimitiveSignature Op where
  argument
    | .first => inputType
    | .second => bit
    | .third => .product bit inputType
  reply
    | .first => bit
    | .second => .unit
    | .third => bit

private def packets (i : Fin 3) : PacketType := if i.val = 1 then inputType else .unit
private def outputs (i : Fin 2) : PacketType := if i.val = 0 then .unit else .product bit bit

-- The third request uses both the entry packet and the first reply.
-- The second declared exit returns the first and third replies.
private def requests : Flat Op 5 1 :=
  .let₁ (.op .first (.bv 0)) (.let₁ (.op .second (.bv 0))
    (.let₁ (.op .third (.pair (.bv 1) (.bv 2))) (.br 4 (.pair (.bv 2) (.bv 0)))))

private def original : FiniteCFG Op 3 2 0 where
  entry := .br 0 .unit
  block i :=
    if i.val = 0 then .br 1 (.pair (.bv 0) .unit)
    else if i.val = 1 then requests
    else .br 3 .unit

private def checked : Checked sig .nil packets outputs original :=
  (check sig .nil packets outputs original (some 1)).get (by decide)

private def built :=
  (construct sig (fun i => (checked.shape.table i).1) outputs checked.emitted.code).get (by decide)

private def dispatcher := built.program

example : checked.shape.selected.val = 1 := rfl
example : checked.shape.row.requests = 3 := rfl
example : dispatcher.locals = 6 := rfl
example : (checked.emitted.code.block 0).erase = .br 1 (.pair (.var 0) .unit) := rfl
example : (checked.emitted.code.block 2).erase = .br 6 .unit := rfl

private def inputPacket : Denote inputType := (⟨⟩, ⟨⟩)
private def initial : dispatcher.State := by
  refine ⟨⟨.inl ⟨1, by decide⟩, ?_⟩⟩
  exact inputPacket

private def askFirst : sig.Request := ⟨.first, inputPacket⟩
private def askSecond (value : Denote bit) : sig.Request := ⟨.second, value⟩
private def askThird (value : Denote bit) : sig.Request := ⟨.third, (value, inputPacket)⟩

private def afterFirst (first : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨3, by decide⟩, ?_⟩⟩
  change Denote inputType × Denote bit
  exact (inputPacket, first)

private def afterSecond (first : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨4, by decide⟩, ?_⟩⟩
  change (Denote inputType × Denote bit) × PUnit
  exact ((inputPacket, first), ⟨⟩)

private def afterThird (first third : Denote bit) : dispatcher.State := by
  refine ⟨⟨.inl ⟨5, by decide⟩, ?_⟩⟩
  change ((Denote inputType × Denote bit) × PUnit) × Denote bit
  exact (((inputPacket, first), ⟨⟩), third)

private def returned (first third : Denote bit) : dispatcher.State :=
  ⟨⟨.inr 1, (first, third)⟩⟩

example : dispatcher.step (dispatcher.start 0 ⟨⟩) = .inr initial := rfl
example : dispatcher.step initial = .inl (.request askFirst afterFirst) := rfl
example (first : Denote bit) :
    dispatcher.step (afterFirst first) = .inl (.request (askSecond first) fun _ => afterSecond first) := rfl
example (first : Denote bit) :
    dispatcher.step (afterSecond first) = .inl (.request (askThird first) (afterThird first)) := rfl
example (first third : Denote bit) : dispatcher.step (afterThird first third) = .inr (returned first third) := rfl

private def emptyEnv : Env Atom := fun _ => .unit

private theorem codec_id (value : Value Atom) : valueCodec id value = value := by
  induction value <;> simp_all only [valueCodec, id_eq]

private theorem primitiveAgreement : PrimitivesAgree sig.primitive sig.primitive id := by
  intro op value
  rw [codec_id, show valueCodec (id : Atom → Atom) = id from funext codec_id, id_map]

theorem packed_observation :
    (region sig.primitive emptyEnv original.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      built.packed.observe emptyEnv emptyEnv := by
  have codec : resultCodec (id : Atom → Atom) = id := by
    funext out
    cases out
    simp only [resultCodec, codec_id, id_eq]
  simpa only [codec, id_map] using
    checked.emitted.public_run built emptyEnv emptyEnv emptyEnv id primitiveAgreement rfl

theorem dispatcher_observation :
    (region sig.primitive emptyEnv original.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      (dispatcher.observe 0 ⟨⟩ >>= fun out => pure (FiniteCFG.packedTreeOutput out)) :=
  packed_observation.trans (built.packed.observe_eq ⟨⟩ _ _ (fun _ => rfl))

-- An explicit selection must be reachable by the certified entry route.
example : (check sig .nil packets outputs original (some 2)).isNone = true := rfl

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.Examples
