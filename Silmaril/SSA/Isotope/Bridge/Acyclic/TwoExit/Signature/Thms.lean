module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Signature.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TwoExitSignature

/-! # Native regions and exact tagged code commute with signature change -/

public section

universe u v w x y z

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open Morphism (SignatureMap)

variable {Φ : Type u} {Ψ : Type v} {τ : Type w} {υ : Type x} {ε : Type y} {δ : Type z}
  [TypeFormers τ] [TypeFormers υ] [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ]
  (g : SignatureMap Φ Ψ τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {A B : τ} {n : Nat} {β : BoundCtx τ n}

/-- The native two-exit region changes only the primitive instructions. -/
theorem toSSA_mapSignature (c : TwoExit Φ A B β) :
    (c.mapSignature g).toSSA = c.toSSA.mapInstr g.instr :=
  toSSA_mapSignature_proof g c

/-- Encoding commutes with the typed code map after transporting the
chosen coproduct type along its preservation equation. -/
theorem encode_mapSignature (c : TwoExit Φ A B β) :
    (c.mapSignature g).encode =
      (SignatureMap.PreservesSums.coprod (g := g) A B ▸ c.encode.mapSignature g :
        Code Ψ (β.mapTypes g.ty) (coprod (g.ty A) (g.ty B))) :=
  encode_mapSignature_proof g c

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
