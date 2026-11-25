module

public import Silmaril.SSA.MLIR.Institution.Translation.Defs
public import Silmaril.SSA.MLIR.Institution.Syntax.Defs
import Silmaril.Proofs.SSA.MLIR.Institution.Translation.Laws

@[expose] public section

namespace Silmaril.MLIR.Institution.Interpretation

open CategoryTheory

variable {withRegions : Bool} {S T U V : Signature withRegions}
variable {n m : Nat} {Γ : Fin n → S.Ty} {Δ : Fin m → S.Ty} {s : S.Ty}

@[simp] theorem term_id (t : Term S Γ s) : (id S).term t = t :=
  Proofs.MLIR.Institution.Translation.term_id t

theorem term_subst (f : Interpretation S T) (t : Term S Γ s) (σ : Block S Δ Γ) :
    f.term (t.subst σ) = (f.term t).subst (fun i => f.term (σ i)) :=
  Proofs.MLIR.Institution.Translation.term_subst f t σ

theorem term_comp (f : Interpretation S T) (g : Interpretation T U) (t : Term S Γ s) :
    (f.comp g).term t = g.term (f.term t) :=
  Proofs.MLIR.Institution.Translation.term_comp f g t

@[simp] theorem id_comp (f : Interpretation S T) : (id S).comp f = f :=
  Proofs.MLIR.Institution.Translation.id_comp f

@[simp] theorem comp_id (f : Interpretation S T) : f.comp (id T) = f :=
  Proofs.MLIR.Institution.Translation.comp_id f

theorem assoc (f : Interpretation S T) (g : Interpretation T U) (h : Interpretation U V) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Proofs.MLIR.Institution.Translation.assoc f g h

/-- A term evaluated after lowering agrees with source evaluation in the induced model. -/
theorem denote_term (f : Interpretation S T) (M : Model T) (t : Term S Γ s)
    (env : Assignment M.carrier (f.sort ∘ Γ)) :
    (f.term t).denote M env = t.denote (f.reduct M) env :=
  Proofs.MLIR.Institution.Translation.denote_term f M t env

theorem reduct_comp (f : Interpretation S T) (g : Interpretation T U) (M : Model U) :
    (f.comp g).reduct M = f.reduct (g.reduct M) :=
  Proofs.MLIR.Institution.Translation.reduct_comp f g M

/-- Satisfaction of a lowered equation agrees with satisfaction in the induced model. -/
theorem satisfaction (f : Interpretation S T) (M : Model T) (e : Equation S) :
    (f.equation e).Holds M ↔ e.Holds (f.reduct M) := by
  simp only [Equation.Holds, equation, denote_term]
  rfl

/-- The lowering acts functorially on raw syntax. -/
def syntaxFunctor (f : Interpretation S T) : Syntax.Context S ⥤ Syntax.Context T where
  obj Γ := ⟨Γ.length, f.sort ∘ Γ.ty⟩
  map σ i := f.term (σ i)
  map_id _ := rfl
  map_comp σ τ := funext fun i => f.term_subst (τ i) σ

@[simp] theorem syntax_id (S : Signature withRegions) : (id S).syntaxFunctor = 𝟭 _ :=
  Functor.ext (fun _ => rfl) (fun _ _ σ => by
    change (id S).syntaxFunctor.map σ = 𝟙 _ ≫ σ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact funext fun i => term_id (σ i))

theorem syntax_comp (f : Interpretation S T) (g : Interpretation T U) :
    (f.comp g).syntaxFunctor = f.syntaxFunctor ⋙ g.syntaxFunctor :=
  Functor.ext (fun _ => rfl) (fun _ _ σ => by
    change (f.comp g).syntaxFunctor.map σ = 𝟙 _ ≫ g.syntaxFunctor.map (f.syntaxFunctor.map σ) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact funext fun i => term_comp f g (σ i))

/-- Lowering syntax and then evaluating is evaluation in the induced model. -/
theorem syntax_denote (f : Interpretation S T) (M : Model T) :
    f.syntaxFunctor ⋙ Syntax.denote M = Syntax.denote (f.reduct M) :=
  Functor.ext (fun _ => rfl) (fun _ _ σ =>
    congrArg TypeCat.ofHom (funext fun env => funext fun i => f.denote_term M (σ i) env))

end Silmaril.MLIR.Institution.Interpretation
