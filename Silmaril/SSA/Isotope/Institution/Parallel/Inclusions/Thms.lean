module

public import Silmaril.SSA.Isotope.Institution.Parallel.Inclusions.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Parallel.Inclusions

@[expose] public section

namespace Silmaril.Isotope.Parallel.Institution

open Silmaril.Isotope.Institution Silmaril.Logic.Institution CategoryTheory Semantics

universe u v q

variable {τ ε : Type u} {S S' : InstrSig τ ε} {ν : Type v} [DecidableEq ν]
  {Γ : Ctx ν τ} {D : τ → Type q} {n : Nat} {β : BoundCtx τ n} {A : τ}

namespace Equation

/-- Restrict observation to LetSeq by forgetting parallel pairing and using its native interpreter. -/
theorem ofLetSeq_sat [HasProduct τ] [HasUnit τ] [ProductModel D] [UnitModel D]
    {l r : LetSeq.LocallyNameless.Tm ν S.Instr n}
    (dl : LetSeq.LocallyNameless.Derivation S.Instr Γ β l A)
    (dr : LetSeq.LocallyNameless.Derivation S.Instr Γ β r A) (X : Model D S) :
    ((LetPar.observation Γ D).obj S).Sat X (ofLetSeq dl dr) ↔
      ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D β),
        dl.denote D X.instr γ ρ = dr.denote D X.instr γ ρ := by
  change (ofLetSeq dl dr).Holds X _ ↔ _
  simp only [Equation.Holds, Equation.ofLetSeq, InstitutionProofs.lowerControl_seq, LetPar.denote_derivation]

/-- Restrict observation to LetCase by forgetting parallel pairing and using its native interpreter. -/
theorem ofLetCase_sat [TypeFormers τ] [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    {l r : LetCase.LocallyNameless.Tm ν S.Instr n}
    (dl : LetCase.LocallyNameless.Derivation S.Instr Γ β l A)
    (dr : LetCase.LocallyNameless.Derivation S.Instr Γ β r A) (X : Model D S) :
    ((LetParCase.observation Γ D).obj S).Sat X (ofLetCase dl dr) ↔
      ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D β),
        dl.denote D X.instr γ ρ = dr.denote D X.instr γ ρ := by
  change (ofLetCase dl dr).Holds X _ ↔ _
  simp only [Equation.Holds, Equation.ofLetCase, InstitutionProofs.lowerControl_case, LetParCase.denote_derivation]

theorem ofLetPar_map [TypeFormers τ] (f : S ⟶ S') (φ : Equation S .seq Γ) :
    φ.ofLetPar.map f = (φ.map f).ofLetPar :=
  InstitutionProofs.equation_widen_map f φ

theorem ofLetPar_sat [TypeFormers τ] [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    (φ : Equation S .seq Γ) (X : Model D S) :
    ((LetParCase.observation Γ D).obj S).Sat X φ.ofLetPar ↔
      ((LetPar.observation Γ D).obj S).Sat X φ := by
  change φ.ofLetPar.Holds X _ ↔ φ.Holds X _
  simp only [Equation.Holds, Equation.ofLetPar, InstitutionProofs.lowerControl_case,
    InstitutionProofs.lowerControl_seq, LetParCase.denote_ofLetParDerivation]

end Equation

variable (Γ D) [TypeFormers τ] [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]

/-- The native inclusion is a comorphism over the identity on instruction signatures.
Its reduct is identity on the shared strict model category. -/
def letParCaseInclusion :
    Inst.CoHom ⟨InstrSig τ ε, LetPar.observation Γ D⟩ ⟨InstrSig τ ε, LetParCase.observation Γ D⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨Equation.ofLetPar, 𝟭 _, fun X φ => φ.ofLetPar_sat X⟩
      naturality := by
        intro S S' f
        apply Room.hom_ext
        · exact funext fun φ => (φ.ofLetPar_map f).symm
        · rfl }

end Silmaril.Isotope.Parallel.Institution
