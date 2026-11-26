module

public import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeSyntax

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Morphism (SignatureMap)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

theorem ssaSignatureCorridor_id_proof :
    ssaSignatureCorridor (J := J) (P := P) (Q := P) SignatureMap.id = 𝟙 (ssaRoom J P) := by
  refine Room.hom_ext (funext mapSSASignature_id_proof) (ssaModelFunctor_ext fun K => ?_)
  exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (K.fromShrinkHoms.as.pullback_id _)

theorem ssaSignatureCorridor_comp_proof :
    ssaSignatureCorridor (J := J) (h.comp g) = ssaSignatureCorridor g ≫ ssaSignatureCorridor h := by
  refine Room.hom_ext (funext (mapSSASignature_comp_proof g h)) (ssaModelFunctor_ext fun K => ?_)
  exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (K.fromShrinkHoms.as.pullback_comp g h _ _ _)

theorem ssaSignatureCorridor_primitive_mod_proof {P Q : InstrSig τ ε} (f : P ⟶ Q) :
    (ssaSignatureCorridor (J := J) f.toSignatureMap).mod = (ssaCorridor (J := J) f).mod := by
  refine ssaModelFunctor_ext fun K => ?_
  exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (K.fromShrinkHoms.as.pullback_primitive f _)

end Silmaril.Isotope.Institution.Acyclic
