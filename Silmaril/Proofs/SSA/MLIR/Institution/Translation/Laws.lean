module

public import Silmaril.SSA.MLIR.Institution.Translation.Defs
public import Silmaril.SSA.MLIR.Institution.Thms

public section

namespace Silmaril.Proofs.MLIR.Institution.Translation

open Silmaril.MLIR.Institution

variable {withRegions : Bool} {S T U V : Signature withRegions}
variable {n m : Nat} {Γ : Fin n → S.Ty} {Δ : Fin m → S.Ty} {s : S.Ty}

theorem term_id (t : Term S Γ s) : (Interpretation.id S).term t = t := by
  induction t with
  | var => rfl
  | app op args bodies i ihArgs ihBodies =>
    change Term.app op (fun j => (Interpretation.id S).term (args j))
      (fun r j => (Interpretation.id S).term (bodies r j)) i = _
    rw [funext ihArgs, funext fun r => funext (ihBodies r)]
    rfl

theorem term_subst (f : Interpretation S T) (t : Term S Γ s) (σ : Block S Δ Γ) :
    f.term (t.subst σ) = (f.term t).subst (fun i => f.term (σ i)) := by
  induction t with
  | var => rfl
  | app op args bodies i ihArgs _ =>
    simp only [Term.subst, Interpretation.term]
    rw [funext fun j => ihArgs j σ]
    cases f.image op with
    | forward => rfl
    | expand _ block => exact ((block i).subst_comp _ _).symm

theorem term_comp (f : Interpretation S T) (g : Interpretation T U) (t : Term S Γ s) :
    (f.comp g).term t = g.term (f.term t) := by
  induction t with
  | var => rfl
  | app op args bodies i ihArgs ihBodies =>
    simp only [Interpretation.term]
    change ((f.image op).translate g).instantiate
      (fun j => (f.comp g).term (args j)) (fun r j => (f.comp g).term (bodies r j)) i = _
    rw [funext ihArgs, funext fun r => funext (ihBodies r)]
    cases f.image op with
    | forward => rfl
    | expand _ block => exact (term_subst g (block i) _).symm

theorem id_comp (f : Interpretation S T) : (Interpretation.id S).comp f = f := by
  cases f
  rfl

theorem comp_id (f : Interpretation S T) : f.comp (Interpretation.id T) = f := by
  cases f with
  | mk sort image =>
    change Interpretation.mk sort (fun {_ _} op => _) = Interpretation.mk sort image
    congr 1
    funext a p op
    change (image op).translate (Interpretation.id T) = image op
    cases image op with
    | forward => rfl
    | expand regionless block =>
      exact congrArg (OpImage.expand regionless) (funext fun i => term_id (block i))

theorem assoc (f : Interpretation S T) (g : Interpretation T U) (h : Interpretation U V) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  cases f with
  | mk sort image =>
    change Interpretation.mk (h.sort ∘ g.sort ∘ sort) (fun {_ _} op => _) =
      Interpretation.mk (h.sort ∘ g.sort ∘ sort) (fun {_ _} op => _)
    congr 1
    funext a p op
    change ((image op).translate g).translate h = (image op).translate (g.comp h)
    cases image op with
    | forward => rfl
    | expand regionless block =>
      exact congrArg (OpImage.expand regionless) (funext fun i => (term_comp g h (block i)).symm)

theorem denote_term (f : Interpretation S T) (M : Model T) (t : Term S Γ s)
    (env : Assignment M.carrier (f.sort ∘ Γ)) :
    (f.term t).denote M env = t.denote (f.reduct M) env := by
  induction t with
  | var => rfl
  | app op args bodies i ihArgs ihBodies =>
    simp only [Interpretation.term, Term.denote, Interpretation.reduct]
    cases f.image op with
    | forward target =>
      exact congrArg₂ (fun values regions => M.op target values regions i)
        (funext fun j => ihArgs j env)
        (funext fun r => funext fun params => funext fun j => ihBodies r j params)
    | expand _ block =>
      exact ((block i).denote_subst M _ env).trans
        (congrArg ((block i).denote M) (funext fun j => ihArgs j env))

theorem reduct_comp (f : Interpretation S T) (g : Interpretation T U) (M : Model U) :
    (f.comp g).reduct M = f.reduct (g.reduct M) := by
  change Model.mk (M.carrier ∘ g.sort ∘ f.sort) (fun {_ _} op => _) =
    Model.mk (M.carrier ∘ g.sort ∘ f.sort) (fun {_ _} op => _)
  congr 1
  funext a p op args bodies i
  change ((f.image op).translate g).denote M args bodies i =
    (f.image op).denote (g.reduct M) args bodies i
  cases f.image op with
  | forward => rfl
  | expand _ block => exact denote_term g M (block i) args

end Silmaril.Proofs.MLIR.Institution.Translation
