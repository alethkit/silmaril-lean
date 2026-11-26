module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Sentence.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Sentence

/-! # Exact equation maps preserve both directions of the syntax bridge -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory
open LambdaSSA.Acyclic (Code)

variable {τ ε : Type} [TypeFormers τ] {P Q S : InstrSig τ ε}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

@[simp] theorem mapCode_id {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code P.Instr β A) :
    mapCode (𝟙 P) c = c :=
  mapCode_id_proof c

@[simp] theorem mapCode_comp (g : P ⟶ Q) (h : Q ⟶ S)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code P.Instr β A) :
    mapCode (g ≫ h) c = mapCode h (mapCode g c) :=
  mapCode_comp_proof g h c

@[simp] theorem mapEquation_id (e : SSAEquation P) : mapEquation (𝟙 P) e = e := by
  rcases e with ⟨i, a, b⟩
  simp only [mapEquation, mapCode_id]

@[simp] theorem mapEquation_comp (g : P ⟶ Q) (h : Q ⟶ S) (e : SSAEquation P) :
    mapEquation (g ≫ h) e = mapEquation h (mapEquation g e) := by
  rcases e with ⟨i, a, b⟩
  simp only [mapEquation, mapCode_comp]

/-- The exact sentence map implements the existing primitive relabelling of
the underlying λSSA program. -/
theorem mapCode_toSSA (g : P ⟶ Q) {n : Nat} {β : BoundCtx τ n} {A : τ}
    (c : Code P.Instr β A) (exit : Nat) :
    (mapCode g c).toSSA exit = (c.toSSA exit).mapInstr (InstrSig.Hom.instr g) :=
  mapCode_toSSA_proof g c exit

/-- Compilation commutes with the institution's exact sentence map. -/
theorem compile_natural (g : P ⟶ Q) (e : SSAEquation P) :
    compile (mapEquation g e) = ((LetCase.inst Γ₀).map g).sen (compile e) :=
  compile_natural_proof g e

/-- Reification commutes with the institution's exact sentence map on
typed code, including the retained operand derivations. -/
theorem reify_natural (g : P ⟶ Q) (e : CaseEquation P) :
    reify (((LetCase.inst Γ₀).map g).sen e) = mapEquation g (reify e) :=
  reify_natural_proof g e

end Silmaril.Isotope.Institution.Acyclic
