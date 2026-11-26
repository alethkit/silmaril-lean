module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Specification.Defs

public section

namespace Silmaril.Proofs.Isotope.Institution.Refinement.UB

open CategoryTheory
open Silmaril.Isotope.Institution.Refinement
open Silmaril.Isotope.Institution.Refinement.UB
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel

universe u v

namespace Specification

variable {P Q : UB.Specification.{u,v}}

theorem lift_sound (f : P ⟶ Q) (c : (i : Q.sig.Index) → Nullary Q.sig.sig i)
    (hc : UB.Specification.IsTop Q c) :
    Set.MapsTo (institution.map (extend f.sig (fun i => c ((PSig.toSig f.sig).sort i)))).sen
      (UB.Specification.free P).axioms ((institution.obj Q.sig).closure Q.axioms) := by
  intro s hs
  rcases hs with ⟨p, hp, rfl⟩ | ⟨i, t, rfl⟩
  · change Sentence.map _ (Sentence.map _ p) ∈ _
    rw [← Sentence.map_comp, include_extend]
    exact f.mapsTo hp
  · let d := fun i => c ((PSig.toSig f.sig).sort i)
    apply hc
    refine ⟨(PSig.toSig f.sig).sort i, (PSig.translate (extend f.sig d)).map t, ?_⟩
    exact congrArg (fun upper => ([⟨(PSig.toSig f.sig).sort i,
      (PSig.translate (extend f.sig d)).map t, upper⟩] : Sentence Q.sig))
      (translate_extend_ub f.sig d i)

theorem initial_le_ub (P : UB.Specification.{u,v}) (i : (UB.Specification.free P).sig.Index)
    (x : (UB.Specification.syntacticModel P).algebra.Carrier i) :
    @LE.le _ ((UB.Specification.syntacticModel P).algebra.order i).toLE x
      (UB.Specification.ubClass P i) := by
  refine Quotient.inductionOn x ?_
  intro t
  change (UB.Specification.freeOrder P).Rel t (Expr.ub (i := i))
  exact (institution.obj (UB.Specification.free P).sig).subset_closure
    (UB.Specification.free P).axioms (Or.inr ⟨i, t, rfl⟩)

theorem below_iff (Q : UB.Specification.{u,v}) (c : (i : Q.sig.Index) → Nullary Q.sig.sig i) :
    UB.Specification.IsTop Q c ↔
      ∀ M : OrderedAlgebra Q.sig.sig, M ∈ (institution.obj Q.sig).modelsOf Q.axioms →
        ∀ (i : Q.sig.Index) (t : Q.sig.syn.Carrier i),
          Q.sig.eval M.toAlgebra t ≤ Q.sig.eval M.toAlgebra (constant Q.sig (c i)) := by
  constructor
  · intro h M hM i t
    exact h ⟨i, t, rfl⟩ M hM _ (List.mem_singleton_self _)
  · intro h s hs M hM p hp
    obtain ⟨i, t, rfl⟩ := hs
    obtain rfl := List.mem_singleton.1 hp
    exact h M hM i t

theorem model_without_top (Q : UB.Specification.{u,v}) (i : Q.sig.Index) :
    ∃ M : OrderedAlgebra Q.sig.sig, M ∈ (institution.obj Q.sig).modelsOf Q.axioms ∧
      ¬ ∃ y : M.Carrier i, ∀ x : M.Carrier i, x ≤ y := by
  let A : Algebra Q.sig.sig := {
    Carrier := fun _ => ULift.{max u v} Bool
    op := fun _ _ => ⟨false⟩ }
  let f : Q.sig.syn ⟶ A := { map := fun _ => ⟨false⟩, comm := fun _ _ => rfl }
  let M := discrete A
  refine ⟨M, ?_, ?_⟩
  · intro s _ p _
    change (Q.sig.isInitial.to A).map p.2.1 = (Q.sig.isInitial.to A).map p.2.2
    have hf : Q.sig.isInitial.to A = f := Q.sig.isInitial.hom_ext _ _
    rw [hf]
  · rintro ⟨y, h⟩
    have h₀ : (ULift.up false : M.Carrier i) = y := h ⟨false⟩
    have h₁ : (ULift.up true : M.Carrier i) = y := h ⟨true⟩
    exact Bool.noConfusion (congrArg ULift.down (h₀.trans h₁.symm))

end Specification
end Silmaril.Proofs.Isotope.Institution.Refinement.UB
