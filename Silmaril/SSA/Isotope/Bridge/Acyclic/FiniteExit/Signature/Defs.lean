module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Thms

/-! # Type change at a finite ordered exit interface -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

open Morphism (SignatureMap)
open Institution (InstrSig)
open Institution.Acyclic (mapContextLookup)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {L : LCtx τ}

/-- Relabel types and primitives, leaving every outward label at its original
index in the ordered list. -/
def mapSignature : {n : Nat} → {β : BoundCtx τ n} → FiniteExit P.Instr L β →
    FiniteExit Q.Instr (L.map g.ty) (β.mapTypes g.ty)
  | _, _, .br hi a => .br (mapContextLookup g.ty hi) (a.mapSignature g)
  | _, _, .case (A := A) (B := B) e l r =>
    .case ((e.mapSignature g).castResult (SignatureMap.PreservesSums.coprod (g := g) A B))
      (mapSignature l) (mapSignature r)
  | _, _, .join a b => .join (a.mapSignature g) (mapSignature b)

end Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit
