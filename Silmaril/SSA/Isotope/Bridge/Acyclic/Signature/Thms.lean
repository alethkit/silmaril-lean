module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Signature.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Signature

/-! # Signature naturality of the exact acyclic translations -/

public section

universe u v w x y z

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Code

open Morphism (SignatureMap)
open LetCase.LocallyNameless (Derivation)

variable {Φ : Type u} {Ψ : Type v} {τ : Type w} {υ : Type x} {ε : Type y} {δ : Type z}
  [TypeFormers τ] [TypeFormers υ] [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ]
  (g : SignatureMap Φ Ψ τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- In the existing λSSA syntax, signature change just relabels the primitive instructions. -/
theorem toSSA_mapSignature (c : Code Φ β A) (exit : Nat) :
    (c.mapSignature g).toSSA exit = (c.toSSA exit).mapInstr g.instr :=
  toSSA_mapSignature_proof g c exit

/-- Compilation commutes with signature change on both terms and their exact derivations. -/
theorem toLetCase_mapSignature (c : Code Φ β A) :
    (c.mapSignature g).toLetCase = c.toLetCase.mapSignature g :=
  toLetCase_mapSignature_proof g c

/-- Reifying a renamed derivation agrees with changing the signature of the reified code. -/
theorem ofLetCase_mapSignature {t : LetCase.LocallyNameless.Tm Empty Φ n}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A) :
    ofLetCase (d.mapSignature g) = (ofLetCase d).mapSignature g :=
  ofLetCase_mapSignature_proof g d

/-- Reification into positional syntax depends only on the term, even when
two typing derivations use different types. -/
theorem ofLetCase_toSSA_congr {t : LetCase.LocallyNameless.Tm Empty Φ n}
    {β' : BoundCtx τ n} {A' : τ}
    (d : Derivation Φ (.nil : Ctx Empty τ) β t A)
    (d' : Derivation Φ (.nil : Ctx Empty τ) β' t A') (exit : Nat) :
    (ofLetCase d).toSSA exit = (ofLetCase d').toSSA exit :=
  ofLetCase_toSSA_congr_proof d d' exit

end Silmaril.Isotope.LambdaSSA.Acyclic.Code
