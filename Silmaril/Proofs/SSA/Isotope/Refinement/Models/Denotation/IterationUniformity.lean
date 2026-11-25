module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationSimulation

/-! # Directed uniformity with a result continuation -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.IterModel
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- The right body and result continuation need no effect bound in directed
mixed uniformity. Only the original left body and state map enter the mover. -/
theorem mixed_uniformity (p : Polarity) {e η : ε} {A A' B B' : τ}
    (h : M.Hom A A') (k : M.Hom B B')
    (f : M.Hom A' (coprod B' A')) (g : M.Hom A (coprod B A))
    (he : EffectSystem.iterable e) (hm : EffectSystem.moves p η e)
    (hh : M.hasEffect η h) (hf : M.hasEffect e f)
    (hs : p.orient M.le (M.compose h f)
      (M.compose g (M.desc (M.compose k (M.inl B' A')) (M.compose h (M.inr B' A'))))) :
    p.orient M.le (M.compose h (M.iterate f)) (M.compose (M.iterate g) k) := by
  rw [M.output_naturality]
  apply M.uniformity p he hm hh hf
  simpa only [M.compose_assoc, M.toCaseData.desc_compose,
    M.toCaseData.inl_desc, M.toCaseData.inr_desc, M.identity_compose] using hs

end Silmaril.Isotope.Refinement.Models.IterModel
