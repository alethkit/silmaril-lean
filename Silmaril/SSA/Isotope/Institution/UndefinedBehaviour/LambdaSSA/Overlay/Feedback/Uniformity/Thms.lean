module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Paths
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Relabel

/-! # Feedback uniformity and block relabeling -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open Institution.Observational

universe u v w x

namespace Feedback

variable {τ : Type v} {R S L : List τ} {α : Type w} {σ : Type x}
  {f : Run R L α σ} {g : Run S L α σ} {p : Point R.length α σ} {q : Point S.length α σ}

/-- Equality observes reachable UB and, below it, the set of ordinary outcomes. -/
theorem close_eq_iff :
    close f p = close g q ↔
      (ReachesUB f p ↔ ReachesUB g q) ∧ (¬ ReachesUB f p → outcomes f p = outcomes g q) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.close_eq_iff

namespace Bisimulation

variable {map : Point R.length α σ → Point S.length α σ}

theorem reaches_iff (h : Bisimulation f g map p) :
    Reaches g (map p) q ↔ ∃ a, Reaches f p a ∧ map a = q :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.reaches_iff h

theorem reachesUB_iff (h : Bisimulation f g map p) :
    ReachesUB f p ↔ ReachesUB g (map p) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.reachesUB_iff h

theorem finite_iff (h : Bisimulation f g map p) (o : Outcome L.length α σ) :
    Feedback.Finite f p o ↔ Feedback.Finite g (map p) o :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.finite_iff h o

theorem infinite_iff (h : Bisimulation f g map p) :
    Infinite f p ↔ Infinite g (map p) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.infinite_iff h

/-- A deterministic graph map with backward step lifting preserves feedback. -/
theorem close_eq (h : Bisimulation f g map p) : close f p = close g (map p) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.close_eq h

end Bisimulation

/-- The combined routing preserves the payload type of every return label. -/
theorem LabelMap.mapLabel_type (m : LabelMap R S) (L : List τ) (i : Fin (R ++ L).length) :
    (S ++ L).get (mapLabel m.label L i) = (R ++ L).get i :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.mapLabel_type m L i

/-- Deterministic sliding. Routing the internal outputs of a body into its
block inputs can be moved from the inputs to the outputs of feedback.
The map may identify labels. -/
theorem close_slide (label : LabelMap R S)
    (body : Point S.length α σ → Behaviour (R ++ L).length α σ) (p : Point R.length α σ) :
    close (fun a => body (a.map label.label)) p =
      close (fun a => mapReturns label.label (body a)) (p.map label.label) :=
  (Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.slide_bisimulation label.label body p).close_eq

theorem relabel_bisimulation (e : Fin R.length ≃ Fin S.length) (f : Run R L α σ)
    (p : Point R.length α σ) : Bisimulation f (relabel e f) (Point.map e) p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Uniformity.relabel_bisimulation e f p

/-- Moving the internal labels and destinations together preserves feedback,
including both forms of may-divergence. -/
theorem close_relabel (e : Fin R.length ≃ Fin S.length) (f : Run R L α σ)
    (p : Point R.length α σ) : close (relabel e f) (p.map e) = close f p :=
  (relabel_bisimulation e f p).close_eq.symm

end Feedback

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ R S L : List τ}

/-- Uniformity for exact typed feedback along a type-preserving deterministic
block map. The local transport hypotheses are checked in the given model. -/
theorem denote_feedback_uniform
    {entry : Region Φ Γ (R ++ L)} {entry' : Region Φ Γ (S ++ L)}
    {blocks : (i : Fin R.length) → Region Φ (R.get i :: Γ) (R ++ L)}
    {blocks' : (i : Fin S.length) → Region Φ (S.get i :: Γ) (S ++ L)}
    (map : Feedback.LabelMap R S) (M : Model.{u,w,x} Φ Γ.length) (s : M.σ)
    (h : Feedback.Bisimulation (feedbackRun entry blocks M) (feedbackRun entry' blocks' M)
      (Feedback.Point.map map.label) (.entry s)) :
    denote (.feedback entry blocks) M s = denote (.feedback entry' blocks') M s :=
  h.close_eq

end Silmaril.Isotope.LambdaSSA.UB.Overlay
