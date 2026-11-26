module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Thms
import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

/-! # Forward transport through a case and local join in the Maybe Kleisli category -/

namespace Silmaril.Isotope.Institution.Acyclic.Examples

open CategoryTheory CategoryTheory.Limits
open Silmaril.Calco2019
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical
open LambdaSSA.Acyclic (Code)
open Morphism (SignatureMap)

private inductive Op | flip

private abbrev A : Ty Bool := .base false
private abbrev B : Ty Bool := .base true
private abbrev Bit : Ty Unit := .base ()

local instance : HasTy Op (Ty Bool) where
  src _ := B
  trg _ := A

local instance : HasTy Op (Ty Unit) where
  src _ := Bit
  trg _ := Bit

local instance : HasEff Op Unit where
  eff _ := ()

private def source : InstrSig (Ty Bool) Unit := ⟨Op⟩
private def target : InstrSig (Ty Unit) Unit := ⟨Op⟩

private def collapse : SignatureMap source.Instr target.Instr (Ty Bool) (Ty Unit) Unit Unit where
  instr := id
  ty := Ty.map (fun _ => ())
  eff := id
  source f := by cases f; rfl
  target f := by cases f; rfl
  effect _ := rfl

local instance : collapse.PreservesProducts where
  product _ _ := rfl
  unit := rfl

local instance : collapse.PreservesSums where
  coprod _ _ := rfl
  empty := rfl

-- Both distinct source payload types occur in the discriminant and map to Bit.
example : ¬ Function.Injective collapse.ty := by
  intro h
  have e : A = B := h (show collapse.ty A = collapse.ty B from rfl)
  cases e

private def obj : Ty Unit → Type
  | .base _ => Bool
  | .product s t => obj s × obj t
  | .unit => PUnit
  | .coprod s t => obj s ⊕ obj t
  | .empty => PEmpty

@[instance_reducible] private noncomputable def types : TypeModel (Ty Unit) Type where
  obj := obj
  productIso s t := Iso.refl (obj s × obj t)
  unitIso := Iso.refl PUnit
  coprodIso s t := (Types.binaryCoproductIso (obj s) (obj t)).symm
  emptyIsInitial := Types.isInitialPEmpty

private abbrev MaybeT := Maybe.Types.Model.{0}
private abbrev J := Kleisli.Adjunction.toKleisli (ofTypeMonad MaybeT)

@[instance_reducible] private def instructions : InstructionModel J types target.Instr where
  denote
    | .flip => J.map (TypeCat.ofHom Bool.not)

-- Distinct endomorphisms verify that the witness theorem applies outside thin categories.
example : (𝟙 (J.obj Bool)) ≠ J.map (TypeCat.ofHom Bool.not) := by
  intro h
  have e := congrArg (fun a => a.of false) h
  change (Sum.inl false : MaybeT Bool) = Sum.inl true at e
  cases e

private abbrev ctx : BoundCtx (Ty Bool) 1 := .snoc .nil (.coprod A B)

private def diamond : Code source.Instr ctx A :=
  .join
    (.case ⟨.bv 0, .bv⟩ (.br ⟨.bv 0, .bv⟩) (.br ⟨.op .flip (.bv 0), .op .bv⟩))
    (.br ⟨.bv 0, .bv⟩)

-- The exact source translation uses a nonempty local CFG and both case arms
-- feed its join. Only the right arm applies the Boolean primitive.
example : diamond.toSSA 0 =
    .cfg (.case (.var 0) (.br 0 (.var 0)) (.br 0 (.op .flip (.var 0)))) 1
      (fun _ => .br 1 (.var 0)) := rfl

private theorem typing : LambdaSSA.Region.HasType ctx.toList (diamond.toSSA 0) [A] :=
  diamond.toSSA_hasType rfl

-- Use the existing semantics' witness for this actual CFG. The target
-- witness has the relabelled typing and the same interpreted arrow.
example :
    letI := pullbackInstructions collapse instructions
    let f := denoteRegion J (pullbackTypes collapse types) typing
    ∃ a : J.obj (ctxObj types (ctx.toList.map collapse.ty)) ⟶ J.obj (labelObj types [Bit]),
      (letI := instructions; RegionDenotes J types (mapRegionTyping collapse typing) a) ∧ HEq f a := by
  let _ := pullbackInstructions collapse instructions
  exact mapRegionWitness collapse types instructions (denoteRegion_spec J _ typing)

end Silmaril.Isotope.Institution.Acyclic.Examples
