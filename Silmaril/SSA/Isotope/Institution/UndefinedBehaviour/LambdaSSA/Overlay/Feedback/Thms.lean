module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Graph
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Native

/-! # Directed feedback for explicit LambdaSSA region UB -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open Institution.Observational

universe u v w x

namespace Feedback

variable {τ : Type v} {R L : List τ} {α : Type w} {σ : Type x}
  {f g : Run R L α σ} {p : Point R.length α σ}

/-- Fresh top arises exactly from a finite ordinary path to a UB point. -/
theorem close_eq_top_iff : close f p = ⊤ ↔ ReachesUB f p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.close_eq_top_iff

/-- In the absence of reachable UB, feedback is an ordinary set of outcomes. -/
theorem close_of_noUB (h : ¬ ReachesUB f p) : close f p = ↑(outcomes f p) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.close_of_noUB h

theorem ordinary_close_iff {o : Outcome L.length α σ} :
    (close f p).Ordinary o ↔ ¬ ReachesUB f p ∧ o ∈ outcomes f p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.ordinary_close_iff

/-- One-step unfolding for fresh top. -/
theorem close_top_unfold :
    close f p = ⊤ ↔ f p = ⊤ ∨ ∃ q, Step f p q ∧ close f q = ⊤ :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.close_top_unfold

/-- One-step unfolding for returns, faults, and may-divergence below fresh top. -/
theorem close_ordinary_unfold {o : Outcome L.length α σ} (safe : close f p ≠ ⊤) :
    (close f p).Ordinary o ↔ (f p).Ordinary (external R L o) ∨
      ∃ q, Step f p q ∧ (close f q).Ordinary o :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.close_ordinary_unfold safe

/-- Feedback is monotone even when replacing a component by top removes its
ordinary outgoing edges. -/
theorem close_mono (le : ∀ q, f q ≤ g q) : close f p ≤ close g p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.close_mono le

end Feedback

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ R L : List τ}

theorem feedback_mono {entry next : Region Φ Γ (R ++ L)}
    {blocks after : (i : Fin R.length) → Region Φ (R.get i :: Γ) (R ++ L)}
    (he : Refines.{u,v,w,x} entry next) (hb : ∀ i, Refines.{u,v,w,x} (blocks i) (after i)) :
    Refines.{u,v,w,x} (.feedback entry blocks) (.feedback next after) :=
  fun M _ => Feedback.close_mono fun
    | .entry s => he M s
    | .block i a s => hb i (extendModel M a) s

section

variable (entry : Region Φ Γ (R ++ L))
  (blocks : (i : Fin R.length) → Region Φ (R.get i :: Γ) (R ++ L))
  (M : Model.{u,w,x} Φ Γ.length) (s : M.σ)

theorem denote_feedback_top_iff :
    denote (.feedback entry blocks) M s = ⊤ ↔ Feedback.ReachesUB (feedbackRun entry blocks M) (.entry s) :=
  Feedback.close_eq_top_iff

/-- Below fresh top, divergence comes from a finitely reached component
divergence or from a genuine infinite internal path. -/
theorem denote_feedback_diverges_iff :
    (denote (.feedback entry blocks) M s).Ordinary .diverge ↔
      ¬ Feedback.ReachesUB (feedbackRun entry blocks M) (.entry s) ∧
        (Feedback.Finite (feedbackRun entry blocks M) (.entry s) .diverge ∨
          Feedback.Infinite (feedbackRun entry blocks M) (.entry s)) := by
  change (Feedback.close (feedbackRun entry blocks M) (.entry s)).Ordinary .diverge ↔ _
  rw [Feedback.ordinary_close_iff]
  simp only [Feedback.outcomes, Set.mem_ofPred_eq, eq_self, true_and]

end

theorem nativeFeedback_hasType (entry : UB.Typed (Φ := Φ) Γ (R ++ L))
    (blocks : (i : Fin R.length) → UB.Typed (Φ := Φ) (R.get i :: Γ) (R ++ L)) :
    (nativeFeedback entry blocks).HasType Γ L :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.nativeFeedback_hasType entry blocks

/-- Exactly the return, fault, and may-divergence observations of the native
recursive CFG, for every model of the existing observational institution. -/
theorem denote_native_feedback (entry : UB.Typed (Φ := Φ) Γ (R ++ L))
    (blocks : (i : Fin R.length) → UB.Typed (Φ := Φ) (R.get i :: Γ) (R ++ L))
    (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    denote (.feedback (.native entry) (fun i => .native (blocks i))) M s =
      denote (.native ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.denote_native_feedback entry blocks M s

end Silmaril.Isotope.LambdaSSA.UB.Overlay
