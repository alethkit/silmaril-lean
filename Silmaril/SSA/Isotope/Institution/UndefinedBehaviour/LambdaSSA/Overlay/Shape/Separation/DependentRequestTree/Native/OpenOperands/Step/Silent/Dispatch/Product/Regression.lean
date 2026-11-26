module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Product.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Dispatch.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.ProductRegression

open Category.FiniteIteration hiding Table Row
open CFG.Dependent (Packet pack)
open CFG.Dependent.Native (withExitUB)
open LambdaSSA.Region (packedExitType)
open Syntax (Payload Primitives StatePrimitives model)
open TwoRequest (Tag)

private abbrev Bit : Syntax.Ty := .coprod .unit .unit
private abbrev Labels : List Syntax.Ty := [Bit, Bit, Bit, Bit]

private inductive Op where
  | read
  deriving DecidableEq

private instance : HasTy Op Syntax.Ty := ⟨fun _ => Bit, fun _ => packedExitType [Bit]⟩
private abbrev sig : RequestSignature Op := ⟨fun _ => [Bit], fun _ => rfl⟩

private def zero : Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def one : Payload Bit := ⟨.inr .unit, .inr .unit⟩

private theorem bits (a : Payload Bit) : a ∈ [zero, one] := by
  obtain ⟨_, typed⟩ := a
  cases typed with
  | inl typed => cases typed; exact List.Mem.head _
  | inr typed => cases typed; exact List.Mem.tail _ (List.Mem.head _)

private theorem labelType (i : Fin Labels.length) : Labels.get i = Bit := by
  change (List.replicate 4 Bit)[i.val]'i.isLt = Bit
  exact List.getElem_replicate i.isLt

private def bitAt (i : Fin Labels.length) (a : Payload Bit) : Payload (Labels.get i) :=
  cast (congrArg Payload (labelType i).symm) a

private def configs : ConfigurationEnumeration Labels where
  configs := (List.finRange Labels.length).flatMap fun i => [⟨i, bitAt i zero⟩, ⟨i, bitAt i one⟩]
  complete := fun ⟨i, a⟩ => List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by
    let decoded := cast (congrArg Payload (labelType i)) a
    have readBack : bitAt i decoded = a := by simp [bitAt, decoded]
    rcases List.mem_cons.mp (bits decoded) with eq | right
    · exact List.mem_cons.mpr (.inl (congrArg (fun x => (⟨i, x⟩ : Packet Labels)) (readBack.symm.trans (congrArg (bitAt i) eq))))
    · have eq := List.mem_singleton.mp right
      exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr
        (congrArg (fun x => (⟨i, x⟩ : Packet Labels)) (readBack.symm.trans (congrArg (bitAt i) eq)))))⟩

private def callers : CallerEnumeration Bit := ⟨[zero, one], bits⟩

private def replies : ReplyEnumeration sig where
  packets _ := [⟨0, zero⟩, ⟨0, one⟩]
  complete _ p := by
    obtain ⟨i, a⟩ := p
    obtain rfl := Fin.eq_zero i
    rcases List.mem_cons.mp (bits a) with rfl | other
    · exact List.Mem.head _
    · obtain rfl := List.mem_singleton.mp other
      exact List.Mem.tail _ (List.Mem.head _)

private def block (detour : Bool) (i : Fin Labels.length) : Row sig Labels [Labels.get i, Bit] := by
  if initial : i = 0 then
    subst i
    exact .guarded (.request .read (.var 0) (fun _ => 1) (fun j => by obtain rfl := Fin.eq_zero j; rfl))
  else if branch : i = 1 then
    subst i
    exact if detour then .dispatch (.var 0) 2 3 (.inl (.var 0)) (.inr (.var 0))
      else .dispatch (.var 0) 1 3 (.inl (.var 0)) (.inr (.var 0))
  else if back : i = 2 then
    subst i
    exact .jump 1 (.var 0)
  else
    exact .guarded (.exit 1)

private def endpoint (detour selected : Bool) : Table sig Labels :=
  ⟨0, block detour, fun i => i == (1 : Tag) && selected⟩

private abbrev source := endpoint false false
private abbrev target := endpoint true false
private abbrev marked := endpoint true true

example : source.head configs zero ⟨1, zero⟩ = .diverge := rfl
example : source.head configs zero ⟨1, one⟩ = .exit 1 false := rfl
example : target.head configs zero ⟨1, zero⟩ = .diverge := rfl
example : target.head configs zero ⟨1, one⟩ = .exit 1 false := rfl

-- Entry, left reply into a silent cycle, and right reply into an ordered exit.
example : source.cutoff target callers id id replies configs configs = 3 := rfl
example : source.checkEntries? target source.native target.native callers id id replies configs configs = some true := rfl
example : source.checkEntries? marked source.native marked.native callers id id replies configs configs = some true := rfl
example : marked.checkEntries? source marked.native source.native callers id id replies configs configs = some false := rfl
example : source.checkEntries? target source.native source.native callers id id replies configs configs = none := rfl

-- The left reply agrees. The mismatch requires the right payload at the
-- same reply position and leaves a certified one-reply prefix.
example :
    (match marked.productMismatch? source zero zero replies configs configs with
     | some ((p, q), [edge]) =>
       p.1 == 1 && p.2.val == one.val && q.1 == 1 && q.2.val == one.val && edge.1.2.2.val == one.val
     | _ => false) = true := rfl

example : source.DeterministicRefines.{0,0} target source.native target.native (A := Bit) id id :=
  (Table.checkEntries_accepts_iff (callers := callers) (replies := replies) (left := configs) (right := configs)
    (by rfl) (by rfl)).mp rfl

example : ¬ marked.DeterministicRefines.{0,0} source marked.native source.native (A := Bit) id id :=
  (Table.checkEntries_rejects_iff (callers := callers) (replies := replies) (left := configs) (right := configs)
    (by rfl) (by rfl)).mp rfl

private def returnBit (value : Payload Bit) : StatePrimitives Op Nat := fun _ _ s =>
  .ret (pack (L := [Bit]) ⟨0, value⟩) (s + 1)

example (s : Nat) :
    Shape.denote (withExitUB source.native source.selected) (model (returnBit zero) (source.visible.bindings zero)) s =
      WithTop.some {Outcome.diverge} :=
  (source.observe_entry _ rfl configs zero (returnBit zero) s).trans
    ((source.observe_step configs zero (returnBit zero) ⟨0, zero⟩ s).trans
      (source.observe_step configs zero (returnBit zero) ⟨1, zero⟩ (s + 1)))

example (s : Nat) :
    Shape.denote (withExitUB target.native target.selected) (model (returnBit one) (target.visible.bindings zero)) s =
      WithTop.some {Outcome.ret (1 : Fin 2) .unit (s + 1)} :=
  (target.observe_entry _ rfl configs zero (returnBit one) s).trans
    ((target.observe_step configs zero (returnBit one) ⟨0, zero⟩ s).trans
      (target.observe_step configs zero (returnBit one) ⟨1, one⟩ (s + 1)))

private def fault : StatePrimitives Op Nat := fun _ _ s => .fault (s + 7)

example (s : Nat) :
    Shape.denote (withExitUB marked.native marked.selected) (model fault (marked.visible.bindings zero)) s =
      WithTop.some {Outcome.fault (s + 7)} :=
  (marked.observe_entry _ rfl configs zero fault s).trans
    (marked.observe_step configs zero fault ⟨0, zero⟩ s)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch.ProductRegression
