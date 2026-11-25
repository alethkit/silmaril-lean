module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Defs

/-! # Packing the input of the native LetIter denotation -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (values packType)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- Interpret a native derivation with empty free context on the packed bound object. -/
noncomputable def packedNative (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) :
    (values (signature (τ := τ) (Φ := Φ) pe)).obj
        (valueObj (Φ := Φ) pe (packType (S := signature (τ := τ) (Φ := Φ) pe) (Bridge.BoundCtx.toThesis β))) ⟶
      (values (signature (τ := τ) (Φ := Φ) pe)).obj (valueObj (Φ := Φ) pe A) :=
  (values (signature (τ := τ) (Φ := Φ) pe)).map (packedEnvIso (Φ := Φ) pe β).inv ≫ denoteInSyntax pe d

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
