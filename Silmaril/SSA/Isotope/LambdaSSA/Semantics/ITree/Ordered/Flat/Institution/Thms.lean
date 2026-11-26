module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Institution

/-! # The ordered weak-tree institution for typed flat CFGs -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room Inst)

universe u v

variable {κ : Type (u + 1)} {P Q S : Signature.{u, v} κ} {exits : Nat} {D : Fin exits → Ty κ}

@[simp] theorem Table.map_id (a : Table P D) : a.map (𝟙 P) = a :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.FlatInstitution.table_map_id a

theorem Table.map_comp (g : P ⟶ Q) (h : Q ⟶ S) (a : Table P D) :
    a.map (g ≫ h) = (a.map g).map h :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.FlatInstitution.table_map_comp g h a

@[simp] theorem Sentence.map_id (s : Sentence P) : s.map (𝟙 P) = s := by
  cases s
  simp only [Sentence.map, Table.map_id]

theorem Sentence.map_comp (g : P ⟶ Q) (h : Q ⟶ S) (s : Sentence P) :
    s.map (g ≫ h) = (s.map g).map h := by
  cases s
  simp only [Sentence.map, Table.map_comp]

variable [AtomValues κ] (Events : Type u → Type u)

@[simp] theorem reduct_id (M : Model (κ := κ) Events P.Instr) :
    reduct Events (𝟙 P) M = M :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.FlatInstitution.model_ext_raw (P := P) rfl

theorem reduct_comp (g : P ⟶ Q) (h : Q ⟶ S) (M : Model (κ := κ) Events S.Instr) :
    reduct Events (g ≫ h) M = reduct Events g (reduct Events h M) :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.FlatInstitution.model_ext_raw (P := P) rfl

@[simp] theorem reductFunctor_id (P : Signature.{u, v} κ) :
    reductFunctor Events (𝟙 P) = 𝟭 (room Events P).Mod :=
  CategoryTheory.Functor.ext fun M => congrArg Discrete.mk (reduct_id Events (P := P) M.as)

theorem reductFunctor_comp (g : P ⟶ Q) (h : Q ⟶ S) :
    reductFunctor Events (g ≫ h) = reductFunctor Events h ⋙ reductFunctor Events g :=
  CategoryTheory.Functor.ext fun M => congrArg Discrete.mk (reduct_comp Events g h M.as)

theorem satisfaction (g : P ⟶ Q) (M : Model (κ := κ) Events Q.Instr) (s : Sentence P) :
    Satisfies Events M (s.map g) ↔ Satisfies Events (reduct Events g M) s :=
  (corridor Events g).sat (Discrete.mk M) s

/-- The flat ordered institution as a functor from fixed-type signatures to rooms. -/
@[expose] def roomFunctor : Signature.{u, v} κ ⥤ Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  obj := room Events
  map g := corridor Events g
  map_id P := Room.hom_ext (funext Sentence.map_id)
    (reductFunctor_id Events P)
  map_comp g h := Room.hom_ext (funext (Sentence.map_comp g h))
    (reductFunctor_comp Events g h)

/-- Capture-free typed flat comparisons, with exact ordered packed satisfaction. -/
@[expose] def institution (κ : Type (u + 1)) [AtomValues κ] :
    Inst.{max (u + 1) (v + 1), max (u + 1) v, max (u + 1) v, max (u + 1) v, max (u + 1) v} :=
  ⟨Signature.{u, v} κ, roomFunctor Events⟩

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution
