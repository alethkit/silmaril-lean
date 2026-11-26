module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value

theorem binds_total (slots : List (Binding × Option Value)) (values : List Value) :
    ∃ result, Binds slots values result := by
  by_cases extra : slots.length < values.length
  · exact ⟨_, .surplus extra⟩
  by_cases missing : missingNames (fill slots values) = []
  · exact ⟨_, .assigned (Nat.le_of_not_gt extra) missing⟩
  · exact ⟨_, .missing (Nat.le_of_not_gt extra) missing⟩

private theorem stored_mem {slots : List (Binding × Option Value)} {slot : Binding} {value : Value}
    (present : (slot, value) ∈ savedValues slots) : slot ∈ slots.map Prod.fst := by
  obtain ⟨⟨key, saved⟩, member, equal⟩ := List.mem_filterMap.mp present
  cases saved with
  | none => simp at equal
  | some saved =>
    simp at equal
    exact equal.1 ▸ List.mem_map_of_mem member

private theorem stored_none {slots : List (Binding × Option Value)} {binding : Binding}
    (absent : binding ∉ slots.map Prod.fst) : List.lookup binding (savedValues slots) = none :=
  List.lookup_eq_none_iff.mpr (by
    intro pair member
    have different : binding ≠ pair.1 := fun same => absent (same ▸ stored_mem (by simpa using member))
    simp [bne, different])

private theorem saved_lookup (slots : List (Binding × Option Value)) (unique : (slots.map Prod.fst).Nodup)
    {entry : Binding × Option Value} (present : entry ∈ slots) :
    List.lookup entry.1 (savedValues slots) = entry.2 := by
  induction slots with
  | nil => cases present
  | cons first rest ih =>
    rcases first with ⟨slot, value⟩
    have names := List.nodup_cons.mp unique
    rcases List.mem_cons.mp present with rfl | later
    · cases value with
      | none =>
        change List.lookup slot (savedValues rest) = none
        exact stored_none names.1
      | some value => simp [savedValues]
    · have different : entry.1 ≠ slot := fun equal => names.1 (List.mem_map.mpr ⟨entry, later, equal⟩)
      have beq : (entry.1 == slot) = false := beq_eq_false_iff_ne.mpr different
      cases value <;> simpa [savedValues, List.lookup_cons, beq] using ih names.2 later

private theorem fill_exact (slots : List (Binding × Option Value)) (values : List Value)
    (unique : (slots.map Prod.fst).Nodup) :
    (slots.map fun slot => (slot.1, (List.lookup slot.1 ((slots.map Prod.fst).zip values)).orElse
      (fun () => List.lookup slot.1 (savedValues slots)))) = fill slots values := by
  induction slots generalizing values with
  | nil => rfl
  | cons first rest ih =>
    cases values with
    | nil =>
      change _ = first :: rest
      calc
        _ = (first :: rest).map id := by
          apply List.map_congr_left
          intro entry present
          simp only [List.zip_nil_right, List.lookup_nil, Option.orElse_none, id_eq]
          exact Prod.ext rfl (saved_lookup _ unique present)
        _ = _ := List.map_id _
    | cons value values =>
      rcases first with ⟨slot, saved⟩
      have names := List.nodup_cons.mp unique
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons_self, Option.orElse_some, fill]
      congr 1
      rw [← ih values names.2]
      apply List.map_congr_left
      intro entry present
      have different : entry.1 ≠ slot := fun equal => names.1 (List.mem_map.mpr ⟨entry, present, equal⟩)
      have beq : (entry.1 == slot) = false := beq_eq_false_iff_ne.mpr different
      simp only [List.lookup_cons, beq]
      rw [saved_lookup _ unique (List.mem_cons_of_mem _ present), saved_lookup _ names.2 present]

theorem binding_exact (signature : Signature) (slots : List (Binding × Option Value))
    (positional : signature.positional.map Parameter.slot = slots.map Prod.fst)
    (unique : (slots.map Prod.fst).Nodup)
    (keywords : signature.keywordOnly = []) (varargs : signature.varargs = none)
    (values : List Value)
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Value))}
    (binding : Binds slots values result) :
    bindArguments signature (savedValues slots) ⟨values, []⟩ =
      result.map (fun assigned => ⟨assigned, [], []⟩) := by
  have filled :
      (signature.named.map fun p =>
        (p.slot, (List.lookup p.slot ((slots.map Prod.fst).zip values)).orElse
          (fun () => List.lookup p.slot (savedValues slots)))) = fill slots values := by
    calc
      _ = (signature.positional.map Parameter.slot).map (fun slot =>
          (slot, (List.lookup slot ((slots.map Prod.fst).zip values)).orElse
            (fun () => List.lookup slot (savedValues slots)))) := by
          simp only [Signature.named, keywords, List.append_nil, List.map_map, Function.comp_def]
      _ = _ := by rw [positional, List.map_map]; exact fill_exact slots values unique
  have noSurplus (bound : values.length ≤ slots.length) :
      bindArguments signature (savedValues slots) ⟨values, []⟩ =
        (if (missingNames (fill slots values)).isEmpty then
          .ok ⟨savedValues (fill slots values), [], []⟩
        else .error (.missingArguments (missingNames (fill slots values)))) := by
    have drop : values.drop (slots.map Prod.fst).length = [] := by
      simp [List.drop_eq_nil_iff, bound]
    simp only [bindArguments, positional, drop, List.isEmpty_nil, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, ite_false, List.foldlM_nil]
    let computed := signature.named.map fun p =>
      (p.slot, (List.lookup p.slot ((slots.map Prod.fst).zip values)).orElse
        (fun () => List.lookup p.slot (savedValues slots)))
    change (show Except Silmaril.Languages.Starlark.Lists.Error BoundArguments from do
      if !(missingNames computed).isEmpty then throw (.missingArguments (missingNames computed))
      return ⟨savedValues computed, [], []⟩) = _
    rw [show computed = fill slots values from filled]
    cases (missingNames (fill slots values)).isEmpty <;> rfl
  cases binding with
  | surplus extra =>
    have nonempty : (values.drop slots.length).isEmpty = false := by
      cases h : values.drop slots.length with
      | nil => have bound := List.drop_eq_nil_iff.mp h; omega
      | cons => rfl
    simp only [bindArguments, positional, List.length_map, varargs, nonempty, Bool.not_false,
      Option.isNone_none, Bool.and_self, ite_true]
    rfl
  | missing bound missing =>
    rw [noSurplus bound]
    cases h : missingNames (fill slots values) with
    | nil => exact (missing h).elim
    | cons => rfl
  | assigned bound complete =>
    rw [noSurplus bound, complete]
    rfl

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
