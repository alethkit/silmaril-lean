module

public import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Admissible.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Admissible.Models

/-! Model reconstruction and the diamond comorphism on admissible RVSDG rooms. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG

open CategoryTheory Silmaril.Logic.Institution

universe u v w
variable {Data : Type u} {P Q R : Signature.{u, v} Data}

theorem admissible_induced (m : Model.{u, v, w} P.op) :
    Admissible m.toRVSDG :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- The law recovers the entire target model, independently of the shape of
the graph interpreted in it. -/
theorem induce_extract (m : AdmissibleModel.{u, v, w} P) :
    (extract m).toRVSDG = m.val :=
  AdmissibleProofs.induce_extract m

theorem extract_induced (m : Model.{u, v, w} P.op) :
    extract ⟨m.toRVSDG, admissible_induced m⟩ = m := by
  cases m
  rfl

/-- Extracting after the actual RVSDG reduct gives the native reduct. -/
theorem extract_reduct (h : P ⟶ Q) (m : AdmissibleModel.{u, v, w} Q) :
    extract (reductModel h m) = reduct h (extract m) := rfl

/-- Satisfaction in an admissible target model agrees with satisfaction in
its extracted native interpretation. -/
theorem admissible_satisfaction (e : Equation P) (m : AdmissibleModel.{u, v, w} P) :
    (lowerEquation e).Holds m.val ↔ e.Holds (extract m) := by
  have h := satisfaction e (extract m)
  rw [induce_extract m] at h
  exact h

theorem targetCorridor_id (P : Signature.{u, v} Data) :
    targetCorridor.{u, v, w} (𝟙 P) = 𝟙 (targetRoom.{u, v, w} P) :=
  AdmissibleProofs.targetCorridor_id P

theorem targetCorridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    targetCorridor.{u, v, w} (h ≫ k) = targetCorridor h ≫ targetCorridor k :=
  AdmissibleProofs.targetCorridor_comp h k

/-- The lifted RVSDG rooms with admissible models, indexed by the native
signature category. -/
def targetInst (Data : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max u v (w + 1), max u v (w + 1)} where
  Sign := Signature.{u, v} Data
  I := ⟨targetRoom.{u, v, w}, targetCorridor.{u, v, w}, targetCorridor_id, targetCorridor_comp⟩

/-- The sentence lowering and reverse model extraction at one signature. -/
def comparisonCorridor (P : Signature.{u, v} Data) :
    room.{u, v, w} P ⟶ targetRoom.{u, v, w} P :=
  ⟨lowerEquation, Discrete.functor (fun m => Discrete.mk (extract m)),
    fun m e => admissible_satisfaction e m.as⟩

theorem comparison_natural (h : P ⟶ Q) :
    corridor.{u, v, w} h ≫ comparisonCorridor Q = comparisonCorridor P ≫ targetCorridor h :=
  Room.hom_ext (funext fun e => (lowerEquation_map h e).symm)
    (Discrete.functor_ext fun m => congrArg Discrete.mk (extract_reduct h m).symm)

/-- Comorphism into the existing RVSDG rooms along the lifted signatures,
with model objects restricted by the local Boolean dispatch law. -/
def comparison (Data : Type u) :
    Inst.CoHom (inst.{u, v, w} Data) (targetInst.{u, v, w} Data) where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor, naturality := fun {P Q} h =>
    comparison_natural (P := P) (Q := Q) h }

end Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG
