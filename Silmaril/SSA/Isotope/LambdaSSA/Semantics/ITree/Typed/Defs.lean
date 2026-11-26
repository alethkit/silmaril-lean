module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
public import Silmaril.SSA.Isotope.Bridge.CaseSSA.Thms

/-! # Typed values for the weak ITree interpretation of LambdaSSA -/

@[expose] public section

universe u v q

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed

open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Elgot.ITree

variable {κ : Type u}

/-- The interpretation of atomic sorts. Compound values use the free type
algebra's structural interpretation. -/
class AtomValues (κ : Type u) where
  carrier : κ → Type u

variable [AtomValues κ]

local notation "V" => AtomValues.carrier (κ := κ)

/-- Interpret the structural coercions of the free type algebra. The exact SSA
interpretation uses just the carriers and their product and sum coordinates. -/
def coerce : {A B : Ty κ} → Ty.Subty A B → Ty.denote V A → Ty.denote V B
  | _, _, .refl _, x => x
  | _, _, .trans f g, x => coerce g (coerce f x)
  | _, _, .product f g, (x, y) => (coerce f x, coerce g y)
  | _, _, .coprod f g, x => Sum.map (coerce f) (coerce g) x
  | _, _, .empty _, x => x.elim
  | _, _, .unit _, _ => PUnit.unit

/-- The set-valued structural interpretation used by the Kleisli model. -/
@[reducible] def typeModel : TypeModel (Ty κ) where
  interp := Ty.denote V
  productEquiv _ _ := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, (fun x => x.elim), (fun x => x.elim)⟩
  coe := coerce

attribute [local instance] typeModel

/-- Raw environments agree with the typed encoding at every in-scope index. -/
def EncodesEnv {Γ : VCtx (Ty κ)} (ρ : Monadic.Env Γ) (env : Env (Sigma V)) : Prop :=
  ∀ i A (h : At Γ i A), env i = encodeValue V A (Monadic.Env.get ρ i h)

/-- Expose the position and payload of a dependent-sum label value. -/
def encodeSigma (L : LCtx (Ty κ)) (p : Σ i : Fin L.length, Ty.denote V (L.get i)) :
    Transfer (Sigma V) :=
  (p.1.val, encodeValue V _ p.2)

/-- Erase a typed exit to the raw label and payload. -/
def encodeLabel (L : LCtx (Ty κ)) (x : Monadic.LabelValue L) : Transfer (Sigma V) :=
  encodeSigma L (Monadic.LabelValue.toSigma L x)

/-- Erase the typed payload while retaining a bounded local label. -/
def encodeBlock {n : Nat} {R : Fin n → Ty κ} (x : Monadic.FiniteLabelDen R) : BlockInput (Sigma V) n :=
  (x.1, encodeValue V _ x.2)

/-- The ITree monad at the first universe containing its observations. -/
abbrev ModelTree (E : Type v → Type v) (A : Type (v + 1)) := Tree E A

variable {κ' : Type (v + 1)} [AtomValues κ']
  {E : Type v → Type v} {Φ : Type q} [HasTy Φ (Ty κ')]

local notation "W" => AtomValues.carrier (κ := κ')

/-- A typed primitive and the erased event interpreter agree on encoded
arguments and on the continuation for every reply. -/
def Compatible (M : Silmaril.Isotope.Semantics.InstructionModel (Ty.denote W) Φ (ModelTree E))
    (raw : Primitive E Φ (Sigma W)) : Prop :=
  ∀ f (x : Ty.denote W (instrSrc f)), raw f (encodeValue W _ x) =
    (M.eval f x >>= fun y => pure (encodeValue W _ y))

/-- Regard the typed ITree primitives as categorical Kleisli arrows. -/
@[reducible] def categoricalInstructions [HasEff Φ Bool]
    [InstructionModel Φ (Ty κ') Bool (ModelTree E)] :
    Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel
      (typeJ (m := ModelTree E)) (Categorical.ofMonadicTypeModel (τ := Ty κ')) Φ :=
  Categorical.ofMonadicInstructionModel (τ := Ty κ') (Φ := Φ) (ε := Bool) (m := ModelTree E)

open CategoryTheory in
/-- Evaluating a pure map in the ITree Kleisli category immediately returns its value. -/
theorem mapTree_of {E : Type v → Type v} {X Y : Type (v + 1)} (f : X ⟶ Y) (x : X) :
    (show ModelTree E Y from ((typeJ (m := ModelTree E)).map f).of x) = pure (f x) := rfl

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
