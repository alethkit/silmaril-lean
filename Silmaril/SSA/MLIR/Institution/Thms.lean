module

public import Silmaril.SSA.MLIR.Institution.Defs
import Silmaril.Proofs.SSA.MLIR.Institution.Laws

@[expose] public section

namespace Silmaril.MLIR.Institution

open CategoryTheory Silmaril.Logic.Institution

variable {withRegions : Bool} {S T U : Signature withRegions}
variable {n m k : Nat} {Γ : Fin n → S.Ty} {Δ : Fin m → S.Ty} {Θ : Fin k → S.Ty} {s : S.Ty}

@[simp] theorem Term.map_id (t : Term S Γ s) : t.map (𝟙 S) = t :=
  Proofs.MLIR.Institution.map_id t

theorem Term.map_comp (f : S ⟶ T) (g : T ⟶ U) (t : Term S Γ s) :
    t.map (f ≫ g) = (t.map f).map g :=
  Proofs.MLIR.Institution.map_comp f g t

/-- Evaluating after symbol and sort reindexing agrees with evaluating in the reduct.
In particular, the corresponding region functions agree at every parameter assignment. -/
theorem Term.denote_map (f : S ⟶ T) (M : Model T) (t : Term S Γ s)
    (env : Assignment M.carrier (f.sort ∘ Γ)) :
    (t.map f).denote M env = t.denote (M.reduct f) env :=
  Proofs.MLIR.Institution.denote_map f M t env

@[simp] theorem Term.subst_id (t : Term S Γ s) : t.subst (fun i => .var i) = t :=
  Proofs.MLIR.Institution.subst_id t

theorem Term.subst_comp (t : Term S Γ s) (σ : Block S Δ Γ) (τ : Block S Θ Δ) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) :=
  Proofs.MLIR.Institution.subst_comp t σ τ

theorem Term.map_subst (f : S ⟶ T) (t : Term S Γ s) (σ : Block S Δ Γ) :
    (t.subst σ).map f = (t.map f).subst (fun i => (σ i).map f) :=
  Proofs.MLIR.Institution.map_subst f t σ

theorem Term.denote_subst (M : Model S) (t : Term S Γ s) (σ : Block S Δ Γ)
    (env : Assignment M.carrier Δ) :
    (t.subst σ).denote M env = t.denote M (fun i => (σ i).denote M env) :=
  Proofs.MLIR.Institution.denote_subst M t σ env

@[simp] theorem Equation.map_id (e : Equation S) : e.map (𝟙 S) = e := by
  cases e
  simp only [Equation.map, Term.map_id]
  rfl

theorem Equation.map_comp (f : S ⟶ T) (g : T ⟶ U) (e : Equation S) :
    e.map (f ≫ g) = (e.map f).map g := by
  cases e
  simp only [Equation.map, Term.map_comp]
  rfl

theorem reductFunctor_id (S : Signature withRegions) : reductFunctor (𝟙 S) = 𝟭 _ :=
  Functor.ext (fun M => by cases M; rfl)

theorem reductFunctor_comp (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f :=
  Functor.ext (fun M => by cases M; rfl)

/-- Satisfaction in the target is equivalent to satisfaction in the model reduct. -/
theorem satisfaction (f : S ⟶ T) (M : Model T) (e : Equation S) :
    (e.map f).Holds M ↔ e.Holds (M.reduct f) := by
  simp only [Equation.Holds, Equation.map, Term.denote_map]
  rfl

/-- The shared construction yields a sentence functor and a contravariant model functor
via the existing institution API. -/
def institution : Signature withRegions ⥤ Room.{0, 1, 1} where
  obj := room
  map f := ⟨Equation.map f, reductFunctor f, fun M => satisfaction f M.as⟩
  map_id S := Room.hom_ext (funext Equation.map_id) (reductFunctor_id S)
  map_comp f g := Room.hom_ext (funext (Equation.map_comp f g)) (reductFunctor_comp f g)

/-- The institution over pure regionless dialect signatures. -/
def regionless : ClassicInstitution (Signature false) :=
  ClassicInstitution.ofRoomFunctor institution

/-- The institution over pure dialect signatures with isolated single-block regions. -/
def isolated : ClassicInstitution (Signature true) :=
  ClassicInstitution.ofRoomFunctor institution

end Silmaril.MLIR.Institution
