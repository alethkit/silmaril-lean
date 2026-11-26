module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Proofs

open CategoryTheory
open Silmaril.MLIR.Institution (Assignment Term)
open RVSDG.MLIR.Graph (ofAssignment toAssignment)

variable {Data : Type} {P Q R : Diamond.Institution.Signature.{0, 0} Data}

theorem denote_transport {S : Silmaril.MLIR.Institution.Signature true}
    (M : Silmaril.MLIR.Institution.Model S) {value : S.Ty → Type}
    (decode : ∀ t, M.carrier t ≃ value t) {n : Nat} {ctx : Fin n → S.Ty} {out : S.Ty}
    (term : Term S ctx out) (env : Assignment M.carrier ctx) :
    term.denote (transport M decode) (fun i => decode _ (env i)) =
      decode out (term.denote M env) := by
  induction term with
  | var => rfl
  | app op args bodies i ihArgs ihBodies =>
    simp only [Term.denote, ihArgs, ihBodies, Equiv.symm_apply_apply]

theorem holds_transport {S : Silmaril.MLIR.Institution.Signature true}
    (M : Silmaril.MLIR.Institution.Model S) {value : S.Ty → Type}
    (decode : ∀ t, M.carrier t ≃ value t) (e : Silmaril.MLIR.Institution.Equation S) :
    e.Holds M ↔ e.Holds (transport M decode) := by
  constructor
  · intro holds env i
    let input : Assignment M.carrier e.context := fun j => (decode _).symm (env j)
    have hEnv : (fun j => decode (e.context j) (input j)) = env :=
      funext fun j => (decode _).apply_symm_apply (env j)
    rw [← hEnv, denote_transport, denote_transport, holds input i]
  · intro holds env i
    have equal := holds (fun j => decode _ (env j)) i
    rw [denote_transport, denote_transport] at equal
    exact (decode _).injective equal

private theorem to_ofAssignment {F : Diamond.Ty Data → Type} (ports : List (Diamond.Ty Data))
    (env : Assignment F ports.get) : toAssignment (ofAssignment ports env) = env := by
  induction ports with
  | nil => exact funext fun i => i.elim0
  | cons _ _ ih =>
    funext i
    exact Fin.cases rfl (fun j => congrFun (ih (fun k => env k.succ)) j) i

theorem normalize_eq_induced (M : Model P) :
    M.toPresentation.normalize = Diamond.MLIR.model M.extract := by
  refine congrArg (Silmaril.MLIR.Institution.Model.mk (S := target P) (Val M.toPresentation.value)) ?_
  funext a p op
  cases op with
  | gamma entry exit extra => exact M.gamma entry exit extra
  | simple node =>
    cases node with
    | dispatch out => exact M.dispatch out
    | pure op =>
      funext args bodies i
      have hi := Fin.fin_one_eq_zero i
      subst i
      have noBodies : bodies = fun j => j.elim0 := funext fun j => j.elim0
      rw [noBodies]
      change M.toPresentation.normalize.op (.simple (.pure op)) args (fun j => j.elim0) (0 : Fin 1) =
        M.toPresentation.normalize.op (.simple (.pure op))
          (toAssignment (ofAssignment _ args)) (fun j => j.elim0) (0 : Fin 1)
      exact congrArg (fun input =>
        M.toPresentation.normalize.op (.simple (.pure op)) input (fun j => j.elim0) (0 : Fin 1))
        (to_ofAssignment _ args).symm

theorem satisfaction (M : Model P) (e : Diamond.Institution.Equation P) :
    (translate e).Holds M.base ↔ e.Holds M.extract := by
  have transported := holds_transport M.base M.toPresentation.decode (translate e)
  change (translate e).Holds M.base ↔ (translate e).Holds M.toPresentation.normalize at transported
  rw [normalize_eq_induced M] at transported
  exact transported.trans (satisfaction_induced e M.extract)

theorem transport_inverse {S : Silmaril.MLIR.Institution.Signature true}
    (M : Silmaril.MLIR.Institution.Model S) {value : S.Ty → Type}
    (encode : ∀ t, M.carrier t ≃ value t) :
    transport (transport M encode) (fun t => (encode t).symm) = M := by
  refine congrArg (Silmaril.MLIR.Institution.Model.mk (S := S) M.carrier) ?_
  funext a p op args bodies i
  simp only [transport, Equiv.symm_symm]
  simp only [Equiv.symm_apply_apply]

theorem extract_reduct (h : P ⟶ Q) (M : Model Q) :
    (M.reduct h).extract = Diamond.Institution.reduct h M.extract := rfl

private theorem presentation_reduct_id (M : Presentation P) : M.reduct (𝟙 P) = M := by
  cases M with
  | mk base predicate selector =>
    simp only [Presentation.reduct]
    congr 1
    refine congrArg (Silmaril.MLIR.Institution.Model.mk (S := target P) base.carrier) ?_
    funext a p op
    cases op with
    | gamma => rfl
    | simple node => cases node <;> rfl

private theorem presentation_reduct_comp (h : P ⟶ Q) (k : Q ⟶ R) (M : Presentation R) :
    M.reduct (h ≫ k) = (M.reduct k).reduct h := by
  cases M with
  | mk base predicate selector =>
    simp only [Presentation.reduct]
    congr 1
    refine congrArg (Silmaril.MLIR.Institution.Model.mk (S := target P) base.carrier) ?_
    funext a p op
    cases op with
    | gamma => rfl
    | simple node => cases node <;> rfl

private theorem model_ext {M N : Model P} (equal : M.toPresentation = N.toPresentation) : M = N := by
  cases M
  cases N
  cases equal
  rfl

theorem reduct_id (M : Model P) : M.reduct (𝟙 P) = M :=
  model_ext (presentation_reduct_id M.toPresentation)

theorem reduct_comp (h : P ⟶ Q) (k : Q ⟶ R) (M : Model R) :
    M.reduct (h ≫ k) = (M.reduct k).reduct h :=
  model_ext (presentation_reduct_comp h k M.toPresentation)

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted.Proofs
