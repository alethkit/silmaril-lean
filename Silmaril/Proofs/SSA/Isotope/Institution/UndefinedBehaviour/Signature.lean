module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Defs

public section

namespace Silmaril.Proofs.Isotope.Institution.Refinement.UB

open CategoryTheory
open Silmaril.Isotope.Institution.Refinement (PSig)
open Silmaril.Isotope.Institution.Refinement.UB
open Silmaril.Logic.Metatheory.TheoryModel

universe u v

variable {P Q R : PSig.{u,v,max u v}}

-- For fixed sort maps the argument bijections are determined by their values
-- on matching positions. This also handles transports past equal operation maps.
theorem hom_ext {g h : P ⟶ Q} (hs : (PSig.toSig g).sort = (PSig.toSig h).sort)
    (ho : ∀ {i} (o : P.sig.Op i), HEq ((PSig.toSig g).op o) ((PSig.toSig h).op o))
    (ha : ∀ {i} (o : P.sig.Op i) (j : Fin (Q.sig.arity ((PSig.toSig g).op o)))
      (k : Fin (Q.sig.arity ((PSig.toSig h).op o))), j.val = k.val →
      ((PSig.toSig g).arg o j).val = ((PSig.toSig h).arg o k).val) : g = h := by
  rcases g with ⟨gs, go, ga, hg⟩
  rcases h with ⟨hs', ho', ha', hh⟩
  cases hs
  have e : @go = @ho' := funext fun i => funext fun o => eq_of_heq (ho o)
  cases e
  have e : @ga = @ha' := funext fun i => funext fun o => Equiv.ext fun j =>
    Fin.ext (ha o j j rfl)
  cases e
  rfl

@[simp] theorem include_extend (f : P ⟶ Q) (c : (i : P.Index) → Nullary Q.sig ((PSig.toSig f).sort i)) :
    inclusion P ≫ extend f c = f := by
  cases f
  rfl

theorem extend_unique (f : P ⟶ Q) (c : (i : P.Index) → Nullary Q.sig ((PSig.toSig f).sort i))
    (g : adjoin P ⟶ Q) (hg : inclusion P ≫ g = f)
    (hc : ∀ i, HEq ((PSig.toSig g).op (i := i) none) (c i).val) : g = extend f c := by
  subst f
  apply hom_ext (g := g) (h := extend (inclusion P ≫ g) c) rfl
  · intro i o
    cases o with
    | none => exact hc i
    | some _ => rfl
  · intro i o j k hjk
    cases o with
    | none => exact Fin.elim0 ((PSig.toSig g).arg none j)
    | some o =>
      have e : j = k := Fin.ext hjk
      cases e
      rfl

theorem translate_extend_ub (f : P ⟶ Q) (c : (i : P.Index) → Nullary Q.sig ((PSig.toSig f).sort i))
    (i : P.Index) :
    (PSig.translate (extend f c)).map (Expr.ub (i := i)) = constant Q (c i) := by
  refine (Algebra.Hom.comm (PSig.translate (extend f c)) none (fun j => Fin.elim0 j)).trans ?_
  exact congrArg (Q.syn.op (c i).val) (funext fun j => Fin.elim0 (finCongr (c i).property j))

@[simp] theorem include_map (f : P ⟶ Q) : inclusion P ≫ map f = f ≫ inclusion Q :=
  include_extend _ _

theorem map_id (P : PSig.{u,v,max u v}) : map (𝟙 P) = 𝟙 (adjoin P) := by
  symm
  apply extend_unique _ _ _ _ (fun _ => HEq.rfl)
  simp

theorem map_comp (f : P ⟶ Q) (g : Q ⟶ R) : map (f ≫ g) = map f ≫ map g := by
  symm
  apply extend_unique _ _ _ _ (fun _ => HEq.rfl)
  rw [← Category.assoc, include_map, Category.assoc, include_map, Category.assoc]

theorem collapse_include (P : PSig.{u,v,max u v}) :
    inclusion (adjoin P) ≫ collapse P = 𝟙 (adjoin P) :=
  include_extend _ _

theorem collapse_naturality (f : P ⟶ Q) :
    map (map f) ≫ collapse Q = collapse P ≫ map f := by
  calc
    map (map f) ≫ collapse Q = extend (map f) (fun _ => ⟨none, rfl⟩) := by
      refine extend_unique _ _ _ ?_ ?_
      · rw [← Category.assoc, include_map, Category.assoc, collapse_include, Category.comp_id]
      · intro i; rfl
    _ = collapse P ≫ map f := by
      symm
      refine extend_unique _ _ _ ?_ ?_
      · rw [← Category.assoc, collapse_include, Category.id_comp]
      · intro i; rfl

theorem collapse_map_include (P : PSig.{u,v,max u v}) :
    map (inclusion P) ≫ collapse P = 𝟙 (adjoin P) := by
  calc
    map (inclusion P) ≫ collapse P = map (𝟙 P) := by
      apply extend_unique _ _ _ _ (fun _ => HEq.rfl)
      rw [← Category.assoc, include_map, Category.assoc, collapse_include, Category.comp_id,
        Category.id_comp]
    _ = _ := map_id P

theorem collapse_assoc (P : PSig.{u,v,max u v}) :
    map (collapse P) ≫ collapse P = collapse (adjoin P) ≫ collapse P := by
  calc
    map (collapse P) ≫ collapse P = extend (collapse P) (fun _ => ⟨none, rfl⟩) := by
      refine extend_unique _ _ _ ?_ ?_
      · rw [← Category.assoc, include_map, Category.assoc, collapse_include, Category.comp_id]
      · intro i; rfl
    _ = collapse (adjoin P) ≫ collapse P := by
      symm
      refine extend_unique _ _ _ ?_ ?_
      · rw [← Category.assoc, collapse_include, Category.id_comp]
      · intro i; rfl

end Silmaril.Proofs.Isotope.Institution.Refinement.UB
