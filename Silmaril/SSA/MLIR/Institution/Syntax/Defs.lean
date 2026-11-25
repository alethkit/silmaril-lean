module

public import Silmaril.SSA.MLIR.Institution.Thms

/-! The category of raw pure expressions, with contexts as objects and
simultaneous substitution as composition. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Syntax

open CategoryTheory

variable {withRegions : Bool} {S T : Signature withRegions}

/-- An ordered finite context of sorts from a signature. -/
structure Context (S : Signature withRegions) where
  length : Nat
  ty : Fin length → S.Ty

instance : Category (Context S) where
  Hom Γ Δ := Block S Γ.ty Δ.ty
  id _ i := .var i
  comp σ τ i := (τ i).subst σ
  id_comp σ := funext fun i => (σ i).subst_id
  comp_id _ := rfl
  assoc σ τ υ := funext fun i => ((υ i).subst_comp τ σ).symm

/-- Interpret ordered contexts as products of carriers and blocks as total functions. -/
def denote (M : Model S) : Context S ⥤ Type where
  obj Γ := Assignment M.carrier Γ.ty
  map σ := TypeCat.ofHom (fun env i => (σ i).denote M env)
  map_id _ := rfl
  map_comp σ τ := congrArg TypeCat.ofHom (funext fun env => funext fun i =>
    (τ i).denote_subst M σ env)

/-- Rename a block and reindex its input and output contexts. -/
def map (f : S ⟶ T) : Context S ⥤ Context T where
  obj Γ := ⟨Γ.length, f.sort ∘ Γ.ty⟩
  map σ i := (σ i).map f
  map_id _ := rfl
  map_comp σ τ := funext fun i => (τ i).map_subst f σ

/-- The model and syntax reindexing commute with denotation. -/
theorem map_denote (f : S ⟶ T) (M : Model T) : map f ⋙ denote M = denote (M.reduct f) := by
  refine Functor.ext (fun _ => rfl) (fun _ _ σ => ?_)
  exact congrArg TypeCat.ofHom (funext fun env => funext fun i => (σ i).denote_map f M env)

end Silmaril.MLIR.Institution.Syntax
