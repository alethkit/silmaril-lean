module

public import Silmaril.SSA.MLIR.Institution.Defs

public section

namespace Silmaril.Proofs.MLIR.Institution

open CategoryTheory Silmaril.MLIR.Institution

variable {withRegions : Bool} {S T U : Signature withRegions}
variable {n m k : Nat} {Γ : Fin n → S.Ty} {Δ : Fin m → S.Ty} {Θ : Fin k → S.Ty} {s : S.Ty}

theorem map_id (t : Term S Γ s) : t.map (𝟙 S) = t := by
  induction t with
  | var i => rfl
  | app o args bodies i ihArgs ihBodies =>
      simp only [Term.map]
      rw [show (fun j => (args j).map (𝟙 S)) = args from funext ihArgs,
        show (fun r j => (bodies r j).map (𝟙 S)) = bodies from funext fun r => funext (ihBodies r)]
      rfl

theorem map_comp (f : S ⟶ T) (g : T ⟶ U) (t : Term S Γ s) :
    t.map (f ≫ g) = (t.map f).map g := by
  induction t with
  | var i => rfl
  | app o args bodies i ihArgs ihBodies =>
      simp only [Term.map]
      rw [funext ihArgs, funext fun r => funext (ihBodies r)]
      rfl

theorem denote_map (f : S ⟶ T) (M : Model T) (t : Term S Γ s)
    (env : Assignment M.carrier (f.sort ∘ Γ)) :
    (t.map f).denote M env = t.denote (M.reduct f) env := by
  induction t with
  | var i => rfl
  | app o args bodies i ihArgs ihBodies =>
      simp only [Term.map, Term.denote]
      exact congrArg₂ (fun values regions => M.op (f.symbol o) values regions i)
        (funext fun j => ihArgs j env) (funext fun r => funext fun params => funext fun j =>
          ihBodies r j params)

theorem subst_id (t : Term S Γ s) : t.subst (fun i => .var i) = t := by
  induction t with
  | var i => rfl
  | app o args bodies i ihArgs _ =>
      simp only [Term.subst]
      rw [funext ihArgs]

theorem subst_comp (t : Term S Γ s) (σ : Block S Δ Γ) (τ : Block S Θ Δ) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t with
  | var i => rfl
  | app o args bodies i ihArgs _ =>
      simp only [Term.subst]
      rw [funext fun j => ihArgs j σ]

theorem map_subst (f : S ⟶ T) (t : Term S Γ s) (σ : Block S Δ Γ) :
    (t.subst σ).map f = (t.map f).subst (fun i => (σ i).map f) := by
  induction t with
  | var i => rfl
  | app o args bodies i ihArgs _ =>
      simp only [Term.subst, Term.map]
      rw [funext fun j => ihArgs j σ]
      rfl

theorem denote_subst (M : Model S) (t : Term S Γ s) (σ : Block S Δ Γ)
    (env : Assignment M.carrier Δ) :
    (t.subst σ).denote M env = t.denote M (fun i => (σ i).denote M env) := by
  induction t with
  | var i => rfl
  | app o args bodies i ihArgs _ =>
      simp only [Term.subst, Term.denote]
      rw [funext fun j => ihArgs j σ]

end Silmaril.Proofs.MLIR.Institution
