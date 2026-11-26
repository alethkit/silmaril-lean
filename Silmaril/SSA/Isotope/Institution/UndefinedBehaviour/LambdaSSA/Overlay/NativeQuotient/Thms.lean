module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.CFG

/-! # Observational descent through the native CFG entry quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open Institution.Observational
open LambdaSSA.Region (CfgQuotient TypedRegion cfgSetoid)

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L K : List τ}

/-- Each installed CFG entry equation and congruence preserves ordinary returns,
faults, and external or internal divergence. -/
theorem cfgEquiv_obs {r s : LambdaSSA.Region Φ} (h : LambdaSSA.Region.CfgEquiv Γ r s L) :
    LambdaSSA.Region.Obs.{u,w,x} r s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.cfgEquiv_obs h

theorem nativeDenotation_eq {r s : TypedRegion (Φ := Φ) Γ L}
    (h : LambdaSSA.Region.Obs.{u,w,x} r.val s.val) :
    nativeDenotation.{u,v,w,x} r = nativeDenotation.{u,v,w,x} s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.nativeDenotation_eq h

/-- Interpret a class of the existing native CFG entry quotient in the UB
overlay. The map uses every observational model, including nondeterministic ones. -/
noncomputable def cfgDenotation :
    CfgQuotient (Φ := Φ) Γ L → Denotation.{u,v,w,x} Φ Γ L :=
  Quotient.lift nativeDenotation (fun _ _ h => nativeDenotation_eq (cfgEquiv_obs h))

@[simp] theorem cfgDenotation_mk (r : TypedRegion (Φ := Φ) Γ L) :
    cfgDenotation.{u,v,w,x} (Quotient.mk (cfgSetoid Γ L) r) = nativeDenotation.{u,v,w,x} r :=
  rfl

/-- A quotient class can be used as the source of overlay substitution. The
chosen continuations may contain UB. -/
noncomputable def substCfg (q : CfgQuotient (Φ := Φ) Γ L)
    (k : (i : Fin L.length) → Region Φ (L.get i :: Γ) K) : Denotation.{u,v,w,x} Φ Γ K :=
  fun M s => (cfgDenotation q M s).bind fun i a mid => denote (k i) (extendModel M a) mid

@[simp] theorem substCfg_mk (r : TypedRegion (Φ := Φ) Γ L)
    (k : (i : Fin L.length) → Region Φ (L.get i :: Γ) K) (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    substCfg (Quotient.mk (cfgSetoid Γ L) r) k M s =
      denote (.lsubst (.native ⟨r.val, r.property⟩) k) M s :=
  rfl

variable {R S : List τ}

/-- Use quotient denotations at the entry and every internal label of a model
feedback graph. -/
noncomputable def cfgRun (entry : CfgQuotient (Φ := Φ) Γ (R ++ L))
    (blocks : (i : Fin R.length) → CfgQuotient (Φ := Φ) (R.get i :: Γ) (R ++ L))
    (M : Model.{u,w,x} Φ Γ.length) : Feedback.Run R L M.α M.σ :=
  Feedback.run (cfgDenotation entry M)
    (fun i a mid => cfgDenotation (blocks i) (extendModel M a) mid)

/-- The native recursive CFG represented by the given typed entry and blocks. -/
def cfgRepresentative (entry : TypedRegion (Φ := Φ) Γ (R ++ L))
    (blocks : (i : Fin R.length) → TypedRegion (Φ := Φ) (R.get i :: Γ) (R ++ L)) :
    TypedRegion (Φ := Φ) Γ L :=
  let e : UB.Typed (Φ := Φ) Γ (R ++ L) := ⟨entry.val, entry.property⟩
  let b : (i : Fin R.length) → UB.Typed (Φ := Φ) (R.get i :: Γ) (R ++ L) :=
    fun i => ⟨(blocks i).val, (blocks i).property⟩
  ⟨nativeFeedback e b, nativeFeedback_hasType e b⟩

/-- Closing the graph of quotient classes agrees with interpreting the native
CFG representative in the existing quotient. -/
theorem cfgDenotation_feedback_mk (entry : TypedRegion (Φ := Φ) Γ (R ++ L))
    (blocks : (i : Fin R.length) → TypedRegion (Φ := Φ) (R.get i :: Γ) (R ++ L))
    (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    cfgDenotation (Quotient.mk (cfgSetoid Γ L) (cfgRepresentative entry blocks)) M s =
      Feedback.close (cfgRun (Quotient.mk (cfgSetoid Γ (R ++ L)) entry)
        (fun i => Quotient.mk (cfgSetoid (R.get i :: Γ) (R ++ L)) (blocks i)) M) (.entry s) :=
  (denote_native_feedback ⟨entry.val, entry.property⟩
    (fun i => ⟨(blocks i).val, (blocks i).property⟩) M s).symm

/-- Semantic block relabeling and two-level elimination apply directly to
feedback on the quotient denotations. -/
theorem cfgRun_relabel_staged (entry : CfgQuotient (Φ := Φ) Γ (R ++ L))
    (blocks : (i : Fin R.length) → CfgQuotient (Φ := Φ) (R.get i :: Γ) (R ++ L))
    (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) (perm : Fin R.length ≃ Fin S.length)
    (inside : Feedback.Point S.length M.α M.σ → Prop) :
    ((Feedback.Graph.ofRun (Feedback.relabel perm (cfgRun entry blocks M))).outer inside).close (.entry s) =
      Feedback.close (cfgRun entry blocks M) (.entry s) :=
  (Feedback.close_partition _ inside _).trans (Feedback.close_relabel perm _ (.entry s))

end Silmaril.Isotope.LambdaSSA.UB.Overlay
