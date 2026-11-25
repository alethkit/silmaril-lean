module

public import Init.Data.List.Perm

/-! # Cambridge structural subtyping

Slides 207–214 of `sewell2026semantics` give these rules on the types of §5.5.
The type view exposes the outer constructor and its immediate children.
It lets the rules use the same types as the typing judgment.
-/

public section

namespace Silmaril.Courses.Cambridge.Subtyping

universe u v

/-- The parts of an L3 type inspected by the subtyping rules. -/
inductive TypeForm (Ty : Type u) (Label : Type v) where
  | atom
  | function (domain codomain : Ty)
  | product (left right : Ty)
  | sum (left right : Ty)
  | record (fields : List (Label × Ty))
  | reference (contents : Ty)

/-- Section 5.5 requires distinct record labels and retains field order. -/
structure TypeView (Ty : Type u) (Label : Type v) where
  form : Ty → TypeForm Ty Label
  distinctLabels : ∀ {type fields}, form type = .record fields →
    (fields.map Prod.fst).Nodup

variable {Ty : Type u} {Label : Type v}

/-- The declarative rules, with explicit reflexivity and transitivity.
The sum rule answers Exercise 34. References use reflexivity and transitivity. -/
inductive Subty (view : TypeView Ty Label) : Ty → Ty → Prop where
  | refl (type : Ty) : Subty view type type
  | trans {source middle target : Ty} :
      Subty view source middle → Subty view middle target → Subty view source target
  | recordWidth {source target : Ty} {kept dropped : List (Label × Ty)} :
      view.form source = .record (kept ++ dropped) → view.form target = .record kept →
      Subty view source target
  /-- Each triple gives a label and the corresponding source and target field types. -/
  | recordDepth {source target : Ty} (fields : List (Label × Ty × Ty)) :
      view.form source = .record (fields.map fun (label, sourceType, _) => (label, sourceType)) →
      view.form target = .record (fields.map fun (label, _, targetType) => (label, targetType)) →
      (∀ {label sourceType targetType}, (label, sourceType, targetType) ∈ fields →
        Subty view sourceType targetType) →
      Subty view source target
  | recordOrder {source target : Ty} {sourceFields targetFields : List (Label × Ty)} :
      view.form source = .record sourceFields → view.form target = .record targetFields →
      sourceFields.Perm targetFields → Subty view source target
  | function {source target domain codomain domain' codomain' : Ty} :
      view.form source = .function domain codomain →
      view.form target = .function domain' codomain' →
      Subty view domain' domain → Subty view codomain codomain' → Subty view source target
  | product {source target left right left' right' : Ty} :
      view.form source = .product left right → view.form target = .product left' right' →
      Subty view left left' → Subty view right right' → Subty view source target
  | sum {source target left right left' right' : Ty} :
      view.form source = .sum left right → view.form target = .sum left' right' →
      Subty view left left' → Subty view right right' → Subty view source target

end Silmaril.Courses.Cambridge.Subtyping
