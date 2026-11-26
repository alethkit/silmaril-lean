module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Comparison.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.TypeChange.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Institution.Quotient.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Lift.Thms
import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

/-! # Forward transport through a case and local join in the Maybe Kleisli category -/

namespace Silmaril.Isotope.Institution.Acyclic.Examples

open CategoryTheory CategoryTheory.Limits
open Silmaril.Calco2019
open Silmaril.SSA.LambdaRTL.Quotient (semSetoid)
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

-- The carrier identifications in the actual algebra reduct support readback
-- even when the type map identifies distinct payload types.
example (K : ValidatedCaseAlgebra J target) :
    (K.reduct collapse).expand =
      K.expand.pullbackOfWitness collapse (regionWitnessPullback collapse K.expand) :=
  ValidatedCaseAlgebra.expand_reduct collapse K

private def mismatchedBranch : LambdaSSA.Region source.Instr := .br 0 (.var 0)

private theorem mismatchedBranch_untyped :
    ¬ LambdaSSA.Region.HasType [A] mismatchedBranch [B] := by
  intro h
  cases h with
  | br hl ha =>
    cases ha with
    | var hv =>
      have e : A = B := (Option.some.inj hv).trans (Option.some.inj hl).symm
      cases e

private theorem mismatchedBranch_image :
    LambdaSSA.Region.HasType ([A].map collapse.ty) (mismatchedBranch.mapInstr collapse.instr)
      ([B].map collapse.ty) :=
  .br rfl (.var rfl)

-- The mapped branch has a witness in the same non-thin Kleisli category;
-- no arrow can witness its preimage at the specified source interfaces.
example :
    (letI := instructions; ∃ a, RegionDenotes J types mismatchedBranch_image a) ∧
      ¬ LambdaSSA.Region.HasType [A] mismatchedBranch [B] := by
  let _ := instructions
  exact ⟨regionDenotes_exists J types mismatchedBranch_image, mismatchedBranch_untyped⟩

example (K : CoherentRegionModel J target) : ¬ RegionWitnessLifts collapse K :=
  fun lift => mismatchedBranch_untyped ((regionWitnessLifts_iff collapse K).mp lift mismatchedBranch_image)

section Composite

private abbrev Wide : Ty Nat := .base 7

local instance : HasTy Op (Ty Nat) where
  src _ := Wide
  trg _ := Wide

local instance : HasEff Op Bool where
  eff _ := true

private def widened : InstrSig (Ty Nat) Bool := ⟨Op⟩

private def widen : SignatureMap target.Instr widened.Instr (Ty Unit) (Ty Nat) Unit Bool where
  instr := id
  ty := Ty.map (fun _ => 7)
  eff := fun _ => true
  source f := by cases f; rfl
  target f := by cases f; rfl
  effect f := by cases f; rfl

local instance : widen.PreservesProducts where
  product _ _ := rfl
  unit := rfl

local instance : widen.PreservesSums where
  coprod _ _ := rfl
  empty := rfl

private def narrow : SignatureMap widened.Instr target.Instr (Ty Nat) (Ty Unit) Bool Unit where
  instr := id
  ty := Ty.map (fun _ => ())
  eff := fun _ => ()
  source f := by cases f; rfl
  target f := by cases f; rfl
  effect f := by cases f; rfl

local instance : narrow.PreservesProducts where
  product _ _ := rfl
  unit := rfl

local instance : narrow.PreservesSums where
  coprod _ _ := rfl
  empty := rfl

-- This nonidentity map reflects typing via a constructor-preserving retraction.
example : RegionTypingReflects widen := by
  have types : Function.LeftInverse narrow.ty widen.ty := by
    intro T
    change Ty.map (fun _ : Nat => ()) (Ty.map (fun _ : Unit => 7) T) = T
    rw [Ty.map_map]
    exact Ty.map_id T
  intro Γ r L h
  exact regionTypingReflects_of_split widen narrow types (fun _ => rfl) h

private def exitsImmediately : LambdaSSA.Region target.Instr :=
  .cfg (.br 1 .unit) 1 (fun _ => .br 1 .unit)

private abbrev targetLayout : Fin 1 → Ty Nat := fun _ => .base 8

-- The same judgement admits a source layout and a target-only layout because
-- the local parameter is unused. The latter layout itself has no preimage.
example : LambdaSSA.Region.HasType ([] : List (Ty Unit)) exitsImmediately [unit] :=
  .cfg (fun _ => (unit : Ty Unit)) (.br rfl .unit) (fun _ => .br rfl .unit)

example : LambdaSSA.Region.HasType ([] : List (Ty Nat))
    (exitsImmediately.mapInstr widen.instr) [unit] :=
  .cfg targetLayout (.br rfl .unit) (fun _ => .br rfl .unit)

example : ¬ ∃ R : Fin 1 → Ty Unit, widen.ty ∘ R = targetLayout := by
  rintro ⟨R, h⟩
  have e := congrFun h 0
  cases hR : R 0 <;> simp [widen, Function.comp_apply, hR] at e

private abbrev p : TypeSignature := ⟨Ty Bool, Unit, source⟩
private abbrev q : TypeSignature := ⟨Ty Unit, Unit, target⟩
private abbrev s : TypeSignature := ⟨Ty Nat, Bool, widened⟩
private def f : p ⟶ q := ⟨collapse⟩
private def g : q ⟶ s := ⟨widen⟩

private def equation : SSAEquation source :=
  ⟨⟨1, ctx, A⟩, diamond,
    .case ⟨.bv 0, .bv⟩ (.br ⟨.bv 0, .bv⟩) (.br ⟨.op .flip (.bv 0), .op .bv⟩)⟩

-- The composite changes the equation's context, result, and effect universe.
example : ((ssaTypeInst J).map (f ≫ g)).sen equation =
    ((ssaTypeInst J).map g).sen (((ssaTypeInst J).map f).sen equation) :=
  mapSSASignature_comp collapse widen equation

example : (((ssaTypeInst J).map (f ≫ g)).sen equation : SSAEquation widened).1 =
    ⟨1, .snoc .nil (.coprod Wide Wide), Wide⟩ := rfl

-- The actual LetCase presentation and exact SSA equation agree on the
-- composite with the bundled reification component.
example : reify ((letCaseTypeInst.map (f ≫ g)).sen (compile equation)) =
    ((ssaTypeInst J).map (f ≫ g)).sen (reify (compile equation)) := by
  change reify (PresSig.mapEquation (typeCaseHom (widen.comp collapse)) (compile equation)) = _
  exact (congrArg (reify (P := widened))
    (typeCaseHom_translate (widen.comp collapse) (compile equation))).trans
      (reify_mapCaseSignature (widen.comp collapse) (compile equation))

-- The inverse comparison commutes with the composite as a corridor,
-- including its action on the validated model category.
example : (ssaTypeInst J).map (f ≫ g) ≫ (validatedCompileNatural J).app s =
    (validatedCompileNatural J).app p ≫
      ((validatedTypeInst J).map f ≫ (validatedTypeInst J).map g) := by
  rw [← CategoryTheory.Functor.map_comp]
  exact (validatedCompileNatural J).naturality (f ≫ g)

private def sequentialLet : SSAEquation source :=
  ⟨⟨0, .nil, unit⟩, .let₁ ⟨.unit, .unit⟩ (.br ⟨.bv 0, .bv⟩), .br ⟨.unit, .unit⟩⟩

-- The round trip reifies a straight-line let as a join.
example : reify (compile sequentialLet) ≠ sequentialLet := by
  intro h
  have e := congrArg (fun φ : SSAEquation source => φ.2.1.toSSA 0) h
  cases e

example (K : (ssaRoom J source).Mod) :
    (ssaRoom J source).Sat K (reify (compile sequentialLet)) ↔
      (ssaRoom J source).Sat K sequentialLet :=
  reify_compile_sat K sequentialLet

-- The distinct exact equations represent the same semantic class.
example : Quotient.mk (semSetoid (ssaRoom J source)) (reify (compile sequentialLet)) =
    Quotient.mk (semSetoid (ssaRoom J source)) sequentialLet :=
  reify_compile_class J p (Quotient.mk (semSetoid (ssaRoom J source)) sequentialLet)

-- The semantic identification survives both changes of signature.
example : Quotient.mk (semSetoid (ssaRoom J widened))
    (((ssaTypeInst J).map (f ≫ g)).sen (reify (compile sequentialLet))) =
    Quotient.mk (semSetoid (ssaRoom J widened))
      (((ssaTypeInst J).map (f ≫ g)).sen sequentialLet) :=
  Quotient.sound (semanticEquiv_map_signature (ssaTypeInst J) (f ≫ g)
    (fun K => reify_compile_sat K sequentialLet))

end Composite

end Silmaril.Isotope.Institution.Acyclic.Examples
