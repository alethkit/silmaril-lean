module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Commutative.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

public section

universe u v w z

namespace Silmaril.Calco2019.Proofs.IterationCommutative

open CategoryTheory CategoryTheory.Limits Guardedness IterationTheory
open Silmaril.Semantics.Domain

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}
  {C : FiniteCopowers X} {σ : Signature.{w}} {E : Type z}
  (M : Interpretation C σ E Y) {S T : Type} [Finite S] [Finite T]

local instance finiteSum (I J : Type) [Finite I] [Finite J] : Finite (I ⊕ J) := by
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  exact Finite.of_fintype _

private def sumIso (C : FiniteCopowers X) (S T : Type) [Finite S] [Finite T] :
    P.sum (C.cofan S).pt (C.cofan T).pt ≅ (C.cofan (S ⊕ T)).pt := by
  let forward := P.desc (C.reindex (Sum.inl : S → S ⊕ T)) (C.reindex (Sum.inr : T → S ⊕ T))
  let legs : S ⊕ T → (X ⟶ P.sum (C.cofan S).pt (C.cofan T).pt) :=
    Sum.elim (fun s => (C.cofan S).inj s ≫ P.inl) (fun t => (C.cofan T).inj t ≫ P.inr)
  let back := Cofan.IsColimit.desc (C.colimit (S ⊕ T)) legs
  have step (i : S ⊕ T) : (C.cofan (S ⊕ T)).inj i ≫ back = legs i :=
    Cofan.IsColimit.fac (C.colimit (S ⊕ T)) legs i
  refine ⟨forward, back, ?_, ?_⟩
  · apply P.hom_ext
    · simp only [forward, P.inl_desc_assoc, Category.comp_id]
      apply Cofan.IsColimit.hom_ext (C.colimit S)
      intro s
      rw [C.reindex_inj_assoc, step]
      rfl
    · simp only [forward, P.inr_desc_assoc, Category.comp_id]
      apply Cofan.IsColimit.hom_ext (C.colimit T)
      intro t
      rw [C.reindex_inj_assoc, step]
      rfl
  · apply Cofan.IsColimit.hom_ext (C.colimit (S ⊕ T))
    intro i
    rw [← Category.assoc, step, Category.comp_id]
    cases i with
    | inl s => simp [legs, forward]
    | inr t => simp [legs, forward]

private theorem map_comp {A B D : K} (f : A ⟶ B) (g : B ⟶ D) :
    P.map (𝟙 Y) f ≫ P.map (𝟙 Y) g = P.map (𝟙 Y) (f ≫ g) := by
  apply P.hom_ext <;> simp [Coproducts.map, Category.assoc]

theorem commutative_of_uniform (F : (Guardedness.greatest P).Fixpoints)
    (uniform : C.BaseUniform F) : C.CommutativeIdentities F := by
  intro I J _ _ R p _ route fibers f
  apply Eq.symm
  apply uniform p (f ≫ P.map (𝟙 R) (C.reindex p)) (C.routedBody p route f) True.intro True.intro
  apply Cofan.IsColimit.hom_ext (C.colimit I)
  intro i
  have route_eq : C.reindex (route i) ≫ C.reindex p = C.reindex p := by
    rw [C.reindex_comp, show p ∘ route i = p from funext (fibers i)]
  have row : (C.cofan I).inj i ≫ C.routedBody p route f =
      (C.cofan J).inj (p i) ≫ f ≫ P.map (𝟙 R) (C.reindex (route i)) :=
    Cofan.IsColimit.fac (C.colimit I) _ i
  rw [C.reindex_inj_assoc, ← Category.assoc ((C.cofan I).inj i), row]
  simp only [Category.assoc, map_comp, route_eq]

private theorem uniform_comp_iso (F : (Guardedness.greatest P).Conway) {A B D : K}
    (j : A ⟶ B) (i : B ≅ D) (uniform : F.toFixpoints.UniformAt j) :
    F.toFixpoints.UniformAt (j ≫ i.hom) := by
  intro R f g hf hg square
  let middle := i.hom ≫ f ≫ P.map (𝟙 R) i.inv
  have iso_square : i.hom ≫ f = middle ≫ P.map (𝟙 R) i.hom := by
    have maps : P.map (𝟙 R) i.inv ≫ P.map (𝟙 R) i.hom = 𝟙 (P.sum R D) := by
      rw [map_comp, i.inv_hom_id]
      simp [Coproducts.map]
    simp [middle, Category.assoc, maps]
  have mid_square : j ≫ middle = g ≫ P.map (𝟙 R) j := by
    have maps : P.map (𝟙 R) (j ≫ i.hom) ≫ P.map (𝟙 R) i.inv = P.map (𝟙 R) j := by
      rw [map_comp, Category.assoc, i.hom_inv_id, Category.comp_id]
    unfold middle
    rw [← Category.assoc (i.hom) f, ← Category.assoc j, ← Category.assoc j, square,
      Category.assoc, maps]
  rw [Category.assoc, F.uniform_iso i middle f True.intro hf iso_square]
  exact uniform middle g True.intro hg mid_square

private theorem uniform_inclusion (F : (Guardedness.greatest P).Conway) :
    F.toFixpoints.UniformAt (C.reindex (Sum.inl : S → S ⊕ T)) := by
  let i := sumIso (P := P) C S T
  have arrow : C.reindex (Sum.inl : S → S ⊕ T) = P.inl ≫ i.hom :=
    (P.inl_desc _ _).symm
  rw [arrow]
  let j := P.inl (X := (C.cofan S).pt) (Y := (C.cofan T).pt)
  have uj : F.toFixpoints.UniformAt j := fun _ _ hf hg square => F.uniform_inl _ _ hg hf square
  intro R f g hf hg square
  exact uniform_comp_iso F j i uj f g hf hg square

private theorem solution_surj (F : (Guardedness.greatest P).Conway)
    (commutative : C.CommutativeIdentities F.toFixpoints)
    {g : System σ E S} {h : System σ E T} {p : S → T}
    (surj : Function.Surjective p) (hom : PreservesEquations g h p) (s : S) :
    M.solution F.toFixpoints g s = M.solution F.toFixpoints h (p s) := by
  classical
  let pick (t : T) : S := Classical.choose (surj t)
  have section_eq (t : T) : p (pick t) = t := Classical.choose_spec (surj t)
  let : Finite (Σ t : T, Fin (g (pick t)).slots) := by
    let : Fintype T := Fintype.ofFinite T
    exact Finite.of_fintype _
  let θ := expandedProjection g pick p
  let raw : (C.cofan T).pt ⟶ P.sum Y (C.cofan (ExpandedState g pick)).pt :=
    Cofan.IsColimit.desc (C.colimit T) (fun t => M.branch (representativeBody g pick t))
  have raw_apply (t : T) : (C.cofan T).inj t ≫ raw = M.branch (representativeBody g pick t) :=
    Cofan.IsColimit.fac (C.colimit T) _ t
  obtain ⟨route, fibers, routes⟩ := expansion_routes g pick p hom section_eq
  have small : raw ≫ P.map (𝟙 Y) (C.reindex θ) = M.body h := by
    apply Cofan.IsColimit.hom_ext (C.colimit T)
    intro t
    rw [← Category.assoc, raw_apply, M.branch_reindex, representative_respects g pick p hom section_eq]
    exact (Cofan.IsColimit.fac (C.colimit T) (fun t => M.branch (P := P) (h t)) t).symm
  have large : C.routedBody θ route raw = M.body (expandedSystem g pick) := by
    apply Cofan.IsColimit.hom_ext (C.colimit (ExpandedState g pick))
    intro z₀
    have apply_route : (C.cofan (ExpandedState g pick)).inj z₀ ≫ C.routedBody θ route raw =
        (C.cofan T).inj (θ z₀) ≫ raw ≫ P.map (𝟙 Y) (C.reindex (route z₀)) :=
      Cofan.IsColimit.fac (C.colimit (ExpandedState g pick)) _ z₀
    rw [apply_route, ← Category.assoc, raw_apply, M.branch_reindex, routes z₀]
    exact (Cofan.IsColimit.fac (C.colimit (ExpandedState g pick))
      (fun z => M.branch (P := P) (expandedSystem g pick z)) z₀).symm
  have e := commutative θ (expandedProjection_surjective g pick p section_eq) route fibers raw
  have e' : F.iterate (M.body (expandedSystem g pick)) True.intro =
      C.reindex θ ≫ F.iterate (M.body h) True.intro :=
    calc
      _ = F.iterate (C.routedBody θ route raw) True.intro :=
        congrArg (fun f => F.iterate f True.intro) large.symm
      _ = _ := e
      _ = _ := congrArg (fun f => C.reindex θ ≫ F.iterate f True.intro) small
  refine (M.solution_of_map F.toFixpoints (uniform_inclusion (C := C) F)
    (expanded_inclusion g pick) s).trans ?_
  unfold Interpretation.solution
  rw [e', C.reindex_inj_assoc]
  rfl

theorem solution_commutative_map (F : (Guardedness.greatest P).Conway)
    (commutative : C.CommutativeIdentities F.toFixpoints)
    {g : System σ E S} {h : System σ E T} {p : S → T}
    (hom : PreservesEquations g h p) (s : S) :
    M.solution F.toFixpoints g s = M.solution F.toFixpoints h (p s) := by
  let k : System σ E (S ⊕ T) := Sum.elim (fun i => (g i).mapState Sum.inl)
    (fun j => (h j).mapState Sum.inr)
  let project : S ⊕ T → T := Sum.elim p id
  have project_hom : PreservesEquations k h project := by
    rintro (i | j)
    · change ((g i).mapState Sum.inl).mapState project = h (p i)
      calc
        _ = (g i).mapState p := by cases g i <;> rfl
        _ = _ := hom i
    · change ((h j).mapState Sum.inr).mapState project = h j
      cases h j <;> rfl
  exact (M.solution_of_map F.toFixpoints (uniform_inclusion (C := C) F)
    (g := g) (h := k) (f := Sum.inl) (fun _ => rfl) s).trans
    (solution_surj M F commutative (p := project) (fun j => ⟨.inr j, rfl⟩) project_hom (.inl s))

theorem solution_standard_commutative (F : (Guardedness.greatest P).Conway)
    (commutative : C.CommutativeIdentities F.toFixpoints)
    (g : System σ E S) (h : System σ E T) (s : S) (t : T)
    (same : fix (update g) s = fix (update h) t) :
    M.solution F.toFixpoints g s = M.solution F.toFixpoints h t := by
  obtain ⟨R, finite, k, left, right, root, hl, hr, rfl, rfl⟩ :=
    (least_eq_iff_finite_span g h s t).1 same
  exact (solution_commutative_map M F commutative hl root).symm.trans
    (solution_commutative_map M F commutative hr root)

end Silmaril.Calco2019.Proofs.IterationCommutative
