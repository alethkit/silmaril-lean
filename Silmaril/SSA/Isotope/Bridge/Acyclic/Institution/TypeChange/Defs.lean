module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Thms

/-! # Signatures with changing types and effects -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory
open Morphism (SignatureMap)

/-- A primitive signature together with its type universe and type formers. -/
structure TypeSignature where
  types : Type
  effects : Type
  [formers : TypeFormers types]
  prim : InstrSig types effects

attribute [instance] TypeSignature.formers

namespace TypeSignature

/-- The existing type- and effect-changing maps that preserve the full type syntax. -/
structure Hom (P Q : TypeSignature) where
  signatureMap : SignatureMap P.prim.Instr Q.prim.Instr P.types Q.types P.effects Q.effects
  [products : signatureMap.PreservesProducts]
  [sums : signatureMap.PreservesSums]

attribute [instance] Hom.products Hom.sums

@[ext] theorem Hom.ext {P Q : TypeSignature} {f g : Hom P Q}
    (e : f.signatureMap = g.signatureMap) : f = g := by
  cases f; cases g; cases e; rfl

instance : Category.{0} TypeSignature where
  Hom := Hom
  id _ := ⟨SignatureMap.id⟩
  comp f g := ⟨g.signatureMap.comp f.signatureMap⟩
  id_comp f := Hom.ext f.signatureMap.comp_id
  comp_id f := Hom.ext f.signatureMap.id_comp
  assoc f g h := Hom.ext (SignatureMap.comp_assoc h.signatureMap g.signatureMap f.signatureMap).symm

/-- Include a fixed type and effect universe with its existing primitive maps. -/
def includePrimitive (τ ε : Type) [TypeFormers τ] : InstrSig τ ε ⥤ TypeSignature where
  obj P := ⟨τ, ε, P⟩
  map g := ⟨g.toSignatureMap⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end TypeSignature
end Silmaril.Isotope.Institution.Acyclic
