module

public import Silmaril.Courses.Cambridge.Subtyping.Rules

/-! # Inversion for declarative subtyping

Reflexivity and transitivity can hide which structural rule was used.
Inversion recovers the component judgments needed when extending L3's
progress and preservation arguments with subsumption.
-/

public section

namespace Silmaril.Courses.Cambridge.Subtyping

universe u v

variable {Ty : Type u} {Label : Type v} {view : TypeView Ty Label}

/-- For each target field, the source has a field of the same label with a
subtype of the target field's type. -/
@[expose] def FieldSubty (view : TypeView Ty Label) (source target : List (Label × Ty)) : Prop :=
  ∀ {label type}, (label, type) ∈ target →
    ∃ sourceType, (label, sourceType) ∈ source ∧ Subty view sourceType type

/-- The conclusions that remain after inverting the outermost constructors. -/
private inductive FormSubty (view : TypeView Ty Label) :
    Ty → TypeForm Ty Label → Ty → TypeForm Ty Label → Prop where
  | atom (type : Ty) : FormSubty view type .atom type .atom
  | reference (type contents : Ty) :
      FormSubty view type (.reference contents) type (.reference contents)
  | function {source target domain codomain domain' codomain' : Ty} :
      Subty view domain' domain → Subty view codomain codomain' →
      FormSubty view source (.function domain codomain) target (.function domain' codomain')
  | product {source target left right left' right' : Ty} :
      Subty view left left' → Subty view right right' →
      FormSubty view source (.product left right) target (.product left' right')
  | sum {source target left right left' right' : Ty} :
      Subty view left left' → Subty view right right' →
      FormSubty view source (.sum left right) target (.sum left' right')
  | record {source target : Ty} {sourceFields targetFields : List (Label × Ty)} :
      FieldSubty view sourceFields targetFields →
      FormSubty view source (.record sourceFields) target (.record targetFields)

private theorem FormSubty.refl (type : Ty) (form : TypeForm Ty Label) :
    FormSubty view type form type form := by
  cases form with
  | atom => exact .atom type
  | reference contents => exact .reference type contents
  | function domain codomain => exact .function (.refl domain) (.refl codomain)
  | product left right => exact .product (.refl left) (.refl right)
  | sum left right => exact .sum (.refl left) (.refl right)
  | record _ => exact .record fun mem => ⟨_, mem, .refl _⟩

private theorem FormSubty.trans {source middle target : Ty}
    {sourceForm middleForm targetForm : TypeForm Ty Label}
    (first : FormSubty view source sourceForm middle middleForm)
    (second : FormSubty view middle middleForm target targetForm) :
    FormSubty view source sourceForm target targetForm := by
  cases first with
  | atom => exact second
  | reference => exact second
  | function domain codomain =>
    cases second with
    | function domain' codomain' => exact .function (domain'.trans domain) (codomain.trans codomain')
  | product left right =>
    cases second with
    | product left' right' => exact .product (left.trans left') (right.trans right')
  | sum left right =>
    cases second with
    | sum left' right' => exact .sum (left.trans left') (right.trans right')
  | record fields =>
    cases second with
    | record fields' =>
      apply FormSubty.record
      intro label type mem
      obtain ⟨_, middleMem, middleSub⟩ := fields' mem
      obtain ⟨_, sourceMem, sourceSub⟩ := fields middleMem
      exact ⟨_, sourceMem, sourceSub.trans middleSub⟩

private theorem Subty.formSubty {source target : Ty} (h : Subty view source target) :
    FormSubty view source (view.form source) target (view.form target) := by
  induction h with
  | refl type => exact .refl type _
  | trans _ _ first second => exact first.trans second
  | recordWidth sourceForm targetForm =>
    rw [sourceForm, targetForm]
    exact .record fun mem => ⟨_, List.mem_append_left _ mem, .refl _⟩
  | recordDepth fields sourceForm targetForm depth _ =>
    rw [sourceForm, targetForm]
    apply FormSubty.record
    intro label type mem
    rcases List.mem_map.mp mem with ⟨⟨lab, sourceType, targetType⟩, fieldMem, fieldEq⟩
    change (lab, targetType) = (label, type) at fieldEq
    cases fieldEq
    exact ⟨sourceType, List.mem_map.mpr ⟨_, fieldMem, rfl⟩, depth fieldMem⟩
  | recordOrder sourceForm targetForm perm =>
    rw [sourceForm, targetForm]
    exact .record fun mem => ⟨_, perm.mem_iff.mpr mem, .refl _⟩
  | function sourceForm targetForm domain codomain _ _ =>
    rw [sourceForm, targetForm]
    exact .function domain codomain
  | product sourceForm targetForm left right _ _ =>
    rw [sourceForm, targetForm]
    exact .product left right
  | sum sourceForm targetForm left right _ _ =>
    rw [sourceForm, targetForm]
    exact .sum left right

namespace Subty

theorem atom_inv {source target : Ty} (h : Subty view source target)
    (targetForm : view.form target = .atom) : source = target := by
  have forms := h.formSubty
  rw [targetForm] at forms
  generalize view.form source = form at forms
  cases forms
  rfl

/-- Subtyping preserves the exact type of a mutable reference. -/
theorem reference_inv {source target contents : Ty} (h : Subty view source target)
    (targetForm : view.form target = .reference contents) : source = target := by
  have forms := h.formSubty
  rw [targetForm] at forms
  generalize view.form source = form at forms
  cases forms
  rfl

theorem function_inv {source target domain codomain : Ty} (h : Subty view source target)
    (targetForm : view.form target = .function domain codomain) :
    ∃ sourceDomain sourceCodomain,
      view.form source = .function sourceDomain sourceCodomain ∧
      Subty view domain sourceDomain ∧ Subty view sourceCodomain codomain := by
  have forms := h.formSubty
  rw [targetForm] at forms
  generalize view.form source = form at forms
  cases forms with
  | function domainSub codomainSub => exact ⟨_, _, rfl, domainSub, codomainSub⟩

theorem product_inv {source target left right : Ty} (h : Subty view source target)
    (targetForm : view.form target = .product left right) :
    ∃ sourceLeft sourceRight,
      view.form source = .product sourceLeft sourceRight ∧
      Subty view sourceLeft left ∧ Subty view sourceRight right := by
  have forms := h.formSubty
  rw [targetForm] at forms
  generalize view.form source = form at forms
  cases forms with
  | product leftSub rightSub => exact ⟨_, _, rfl, leftSub, rightSub⟩

theorem sum_inv {source target left right : Ty} (h : Subty view source target)
    (targetForm : view.form target = .sum left right) :
    ∃ sourceLeft sourceRight,
      view.form source = .sum sourceLeft sourceRight ∧
      Subty view sourceLeft left ∧ Subty view sourceRight right := by
  have forms := h.formSubty
  rw [targetForm] at forms
  generalize view.form source = form at forms
  cases forms with
  | sum leftSub rightSub => exact ⟨_, _, rfl, leftSub, rightSub⟩

theorem record_inv {source target : Ty} {targetFields : List (Label × Ty)}
    (h : Subty view source target) (targetForm : view.form target = .record targetFields) :
    ∃ sourceFields, view.form source = .record sourceFields ∧
      FieldSubty view sourceFields targetFields := by
  have forms := h.formSubty
  rw [targetForm] at forms
  generalize view.form source = form at forms
  cases forms with
  | record fields => exact ⟨_, rfl, fields⟩

end Subty

end Silmaril.Courses.Cambridge.Subtyping
