module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Purity.Thms

/-! # Standalone bound simulation for instruction-free state changes -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Certify that a term contains no primitive instructions by marking every
instruction impure in the existing syntactic purity judgment. -/
abbrev InstructionFree (t : Tm Φ) : Prop :=
  @Tm.Pure Φ Bool ⟨fun _ => true⟩ false t

/-- A bind-first form of the companion's `Uniform.uniform`, restricted to
instruction-free state changes. The local square uses the existing Paper
equivalence, so this standalone step can seed a contextual extension.

See [the companion rule](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/Uniform.lean#L40-L48). -/
inductive InstructionFreeStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | simulate {Γ : VCtx τ} {L : LCtx τ} {A D : τ} {entry p q : Region Φ} {t : Tm Φ}
      (he : ValueBranches Γ entry (A :: L))
      (hp : ValueBranches (A :: Γ) p (A :: L))
      (hq : ValueBranches (D :: Γ) q (D :: L))
      (ht : Tm.HasType (A :: Γ) t D) (pure : InstructionFree t)
      (square : Eqv (A :: Γ)
        (p.lsubst (liftLSubstVars (boundLocalMap t)))
        ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) (D :: L)) :
      InstructionFreeStep Γ (.cfg entry 1 (fun _ => p))
        (.cfg (entry.lsubst (boundLocalMap t)) 1 (fun _ => q)) L

end Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
