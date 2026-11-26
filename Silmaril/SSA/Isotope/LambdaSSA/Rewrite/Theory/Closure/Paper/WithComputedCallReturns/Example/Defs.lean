module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs

/-! # A computed argument with two distinct typed opcodes -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example

open Silmaril Silmaril.Isotope.LambdaSSA

abbrev Atom := ULift.{1} Unit

abbrev Payload : Ty Atom := .base ⟨()⟩

inductive Op where
  | produce
  | consume

instance : HasTy Op (Ty Atom) where
  src _ := Payload
  trg _ := Payload

instance : HasEff Op Bool where
  eff _ := true

/-- The caller cannot simply reuse the original argument. It takes the
producer's reply through a local binding. -/
def operand : Tm Op := .let₁ (.op .produce (.var 0)) (.var 0)

def nested : Tm Op := .op .consume operand

def sequenced : Tm Op := .let₁ operand (.op .consume (.var 0))

theorem operand_typed : Tm.HasType [Payload] operand Payload :=
  .let₁ (.op (.var rfl)) (.var rfl)

theorem nested_typed : Tm.HasType [Payload] nested Payload := .op operand_typed

theorem sequenced_typed : Tm.HasType [Payload] sequenced Payload :=
  .let₁ operand_typed (.op (.var rfl))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedCallReturns.Example
