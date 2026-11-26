module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Signature.Thms

/-! # Relabelling the two-exit interface -/

@[expose] public section

universe u v w x y z

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open Morphism (SignatureMap)

variable {Φ : Type u} {Ψ : Type v} {τ : Type w} {υ : Type x} {ε : Type y} {δ : Type z}
  [TypeFormers τ] [TypeFormers υ] [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ]
  (g : SignatureMap Φ Ψ τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {A B : τ}

/-- Relabel operand derivations and preserve both positions in the exit list. -/
def mapSignature : {n : Nat} → {β : BoundCtx τ n} → TwoExit Φ A B β →
    TwoExit Ψ (g.ty A) (g.ty B) (β.mapTypes g.ty)
  | _, _, .left a => .left (a.mapSignature g)
  | _, _, .right b => .right (b.mapSignature g)
  | _, _, .case (X := X) (Y := Y) e l r =>
    .case ((e.mapSignature g).castResult (SignatureMap.PreservesSums.coprod (g := g) X Y))
      (mapSignature l) (mapSignature r)
  | _, _, .dispatch c =>
    .dispatch (SignatureMap.PreservesSums.coprod (g := g) A B ▸ c.mapSignature g)

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
