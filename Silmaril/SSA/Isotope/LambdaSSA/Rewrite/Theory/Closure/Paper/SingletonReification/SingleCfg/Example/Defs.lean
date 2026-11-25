module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

/-! # A captured one-block LambdaSSA example in the Maybe model -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Calco2019
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)

abbrev U : Ty Empty := .unit
abbrev Flag : Ty Empty := .coprod U U
abbrev Carry : Ty Empty := .product Flag Flag
abbrev Exit : Ty Empty := packedExitType [Flag, Flag]

scoped instance : HasTy Empty (Ty Empty) where
  src := Empty.elim
  trg := Empty.elim

/-- Repeat with a right tag from the left state, then return the captured flag. -/
def block : Region Empty :=
  .let₂ (.var 0)
    (.case (.var 0)
      (.br 0 (.inl (.inr .unit)))
      (.br 0 (.inr (.inl (.var 2)))))

theorem blockBound : ValueBranches [Carry] block [Exit] :=
  .let₂ (.var (i := 0) rfl) (.case (.var (i := 0) rfl)
    (.br rfl (.inl (.inr .unit))) (.br rfl (.inr (.inl (.var (i := 2) rfl)))))

abbrev Bits := PUnit.{1} ⊕ PUnit.{1}

/-- Interpret products as pairs and the two sum constructors as tags. -/
def obj : Ty Empty → Type
  | .base a => a.elim
  | .product A B => obj A × obj B
  | .unit => PUnit
  | .coprod A B => obj A ⊕ obj B
  | .empty => PEmpty

/-- The canonical set interpretation of the instruction-free example types. -/
@[instance_reducible] noncomputable def M : TypeModel (Ty Empty) Type where
  obj := obj
  productIso A B := Iso.refl (obj A × obj B)
  unitIso := Iso.refl PUnit
  coprodIso A B := (Types.binaryCoproductIso (obj A) (obj B)).symm
  emptyIsInitial := Types.isInitialPEmpty

abbrev MaybeT := Maybe.Types.Model.{0}
abbrev J := Kleisli.Adjunction.toKleisli (ofTypeMonad MaybeT)

noncomputable scoped instance : InstructionModel J M Empty where denote f := f.elim

/-- The packed block output in constructor coordinates. -/
def blockValue (c s : Bits) : obj Exit :=
  match s with
  | .inl _ => .inl (.inr PUnit.unit)
  | .inr _ => .inr (.inl c)

abbrev Live := labelObj M [Flag]
abbrev Capture := ctxObj M [Flag]
abbrev Carried := Capture ⊗ Live

/-- Embed the capture and state tag in the actual singleton-label carrier. -/
noncomputable def stateInput (c s : Bits) : Carried :=
  ((PUnit.unit, c), labelInject M 0 (rfl : At [Flag] 0 Flag) s)

/-- The retained step of the actual typed packed block. -/
noncomputable def actualStep : J.obj Carried ⟶ J.obj Carried ⨿ J.obj Carried :=
  contextualStep J (blockComputation M J Flag Flag Flag (denoteSingletonRegion J M blockBound.hasType))

/-- Convert the selected computation coproduct to the exact return-or-repeat sum. -/
noncomputable def exactStep : J.obj Carried ⟶ Kleisli.mk (ofTypeMonad MaybeT) (Carried ⊕ Carried) :=
  actualStep ≫ (Kleisli.Type.coprodIsoSum MaybeT (J.obj Carried) (J.obj Carried)).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg.CapturedRecurExit
