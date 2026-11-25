module

public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Silmaril.Logic.Temporal.TLA.General.Thms

/-! # The institution of scoped General TLA over fixed carriers -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.General.Institution

open CategoryTheory
open Silmaril.Inst (Plain)
open Silmaril.Logic.Institution (Room)

universe u

variable {Sorts : Type u}

/-- A sort-preserving renaming with an injective map of flexible names at each sort.
Rigid names of the same sort may be identified. -/
abbrev Hom (Γ Δ : Scope Sorts) := {f : Scope.Rename Γ Δ // f.flex.Injective}

instance scopeCategory : Category.{u} (Scope Sorts) where
  Hom := Hom
  id Γ := ⟨Scope.Rename.id Γ, Context.Rename.injective_id Γ.flex⟩
  comp f g := ⟨f.val.comp g.val, f.property.comp g.property⟩
  id_comp f := Subtype.ext f.val.id_comp
  comp_id f := Subtype.ext f.val.comp_id
  assoc f g h := Subtype.ext (f.val.comp_assoc g.val h.val)

/-- Sentences and models are those of General TLA. Reduct restricts the rigid
valuation and the flexible valuation at every instant of the behavior. -/
def plain (Value : Sorts → Type u) : Plain (Scope Sorts) where
  Sen := Formula Value
  map f p := p.rename f.val
  map_id _ p := p.rename_id
  map_comp f g p := p.rename_comp f.val g.val
  Mod := Model Value
  reduct f M := M.reduct f.val
  reduct_id _ M := M.reduct_id
  reduct_comp f g M := M.reduct_comp f.val g.val
  Sat M p := p.Satisfies M
  sat_map f M p := p.satisfies_rename f.val f.property M

/-- Scoped General TLA as a functor to rooms with discrete categories of models. -/
abbrev roomFunctor (Value : Sorts → Type u) : Scope Sorts ⥤ Room.{u + 1, 0, u} :=
  (plain Value).functor

/-- The packaged institution over the chosen carriers. -/
abbrev institution (Value : Sorts → Type u) : Silmaril.Inst.Institution :=
  (plain Value).toInst

end Silmaril.Logic.Temporal.TLA.General.Institution
