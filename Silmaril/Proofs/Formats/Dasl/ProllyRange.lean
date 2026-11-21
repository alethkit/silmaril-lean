module

public import Silmaril.Formats.Dasl.Prolly.Range.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyRange

open Silmaril.Formats.Dasl.Prolly (Fault)
open Silmaril.Formats.Dasl.Prolly.Range (Result includes selectedVisits scan)
open Silmaril.Semantics.Prolly

variable {Name Key Payload : Type} [LinearOrder Key]

private theorem mapM_sound {Item Output Error : Type} {items : List Item} {fetch : Item → Except Error Output}
    {truth : Item → Output} {results : List Output}
    (sound : ∀ item ∈ items, ∀ found, fetch item = .ok found → found = truth item)
    (checked : items.mapM fetch = .ok results) : results = items.map truth := by
  induction items generalizing results with
  | nil => exact (Except.ok.inj checked).symm
  | cons head tail ih =>
    cases first : fetch head with
    | error err => simp [List.mapM_cons, first, Bind.bind, Except.bind] at checked
    | ok item =>
      have correct := sound head (by simp) item first
      cases rest : tail.mapM fetch with
      | error err => simp [List.mapM_cons, first, rest, Bind.bind, Except.bind] at checked
      | ok items =>
        have tailCorrect := ih (fun next hit => sound next (List.mem_cons_of_mem _ hit)) rest
        simpa [List.mapM_cons, first, rest, Bind.bind, Except.bind, Pure.pure, Except.pure, correct, tailCorrect]
          using checked.symm

private theorem pruned_empty {lower upper separator : Key} {entries : List (Key × Payload)}
    (ordered : entries.Pairwise fun left right => left.1 < right.1)
    (maximum : entries.getLast?.map Prod.fst = some separator) (pruned : ¬ lower ≤ separator) :
    entries.filter (fun entry => includes lower upper entry.1) = [] := by
  obtain ⟨last, lastEq, sep⟩ := Option.map_eq_some_iff.mp maximum
  apply List.filter_eq_nil_iff.mpr
  intro entry present
  have weak : entries.Pairwise (fun left right => left.1 ≤ right.1) := ordered.imp le_of_lt
  have lastBound := weak.rel_getLast_of_rel_getLast_getLast
    present (le_refl (entries.getLast (List.ne_nil_of_mem present)).1)
  rw [List.getLast_of_getLast?_eq_some lastEq, sep] at lastBound
  simp [includes, not_le.mpr (lt_of_le_of_lt lastBound (lt_of_not_ge pruned))]

theorem range_scan_sound {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (width : Nat) (lower upper : Key)
    (fuel level : Nat) (node : Node Key Payload level)
    (ordered : (flatten level node).Pairwise fun left right => left.1 < right.1)
    (separators : Node.Separators level node)
    (agrees : ∀ block ∈ blockOccurrences address level node,
      ∀ actual, read (address block) = .ok actual → actual = block)
    {expected : Option Nat} {result : Result Key Payload}
    (checked : scan read width lower upper fuel expected (address (nodeBlock address level node)) = .ok result) :
    result = ⟨(flatten level node).filter fun entry => includes lower upper entry.1, selectedVisits lower level node⟩ := by
  induction fuel generalizing level expected result with
  | zero => simp [scan] at checked
  | succ fuel ih =>
    have root : nodeBlock address level node ∈ blockOccurrences address level node := by
      cases level <;> simp [blockOccurrences]
    cases seen : read (address (nodeBlock address level node)) with
    | error fault => simp [scan, seen, Bind.bind, Except.bind] at checked
    | ok actual =>
      have eq := agrees _ root actual seen
      subst actual
      simp only [scan, seen, Bind.bind, Except.bind] at checked
      cases level with
      | zero =>
        simp only [nodeBlock] at checked
        split at checked
        · exact (Except.ok.inj checked).symm
        · contradiction
      | succ level =>
        simp only [nodeBlock] at checked
        split at checked
        · simp only [List.mapM_map, Nat.add_sub_cancel] at checked
          let fetch := fun (child : Key × Node Key Payload level) =>
            if lower ≤ child.1 then scan read width lower upper fuel (some level)
              (address (nodeBlock address level child.2)) else .ok ⟨[], 0⟩
          change (node.mapM fetch >>= fun groups =>
            .ok ⟨groups.flatMap Result.entries, 1 + (groups.map Result.visits).sum⟩) = .ok result at checked
          cases fetched : node.mapM fetch with
          | error fault => simp [fetched, Bind.bind, Except.bind] at checked
          | ok groups =>
            let truth := fun (child : Key × Node Key Payload level) =>
              (⟨(flatten level child.2).filter fun entry => includes lower upper entry.1,
                if lower ≤ child.1 then selectedVisits lower level child.2 else 0⟩ : Result Key Payload)
            have exactGroups : groups = node.map truth := by
              apply mapM_sound (checked := fetched)
              intro child member found foundChild
              have orderedChild := (List.pairwise_flatMap.mp ordered).1 child member
              by_cases selects : lower ≤ child.1
              · have exactChild := ih level child.2 orderedChild (separators.2 child member).2
                  (fun block observed actual hit => agrees block (List.mem_cons_of_mem _
                    (List.mem_flatMap.mpr ⟨child, member, observed⟩)) actual hit)
                  (by simpa [fetch, selects] using foundChild)
                simpa [truth, selects] using exactChild
              · have empty := pruned_empty orderedChild (separators.2 child member).1 (upper := upper) selects
                simpa [truth, fetch, selects, empty] using foundChild.symm
            have output : result = ⟨groups.flatMap Result.entries, 1 + (groups.map Result.visits).sum⟩ := by
              simpa [fetched, Bind.bind, Except.bind] using checked.symm
            rw [output, exactGroups]
            simp [truth, flatten, List.filter_flatMap, selectedVisits, List.flatMap_map, Function.comp_def]
        · contradiction

theorem visits_le_all (address : Block Name Key Payload → Name) (lower : Key) (level : Nat)
    (node : Node Key Payload level) : selectedVisits lower level node ≤ (blockOccurrences address level node).length := by
  induction level with
  | zero => rfl
  | succ level ih =>
    simp only [selectedVisits, blockOccurrences, List.length_cons, List.length_flatMap]
    have sums : (node.map fun child => if lower ≤ child.1 then selectedVisits lower level child.2 else 0).sum ≤
        (node.map fun child => (blockOccurrences address level child.2).length).sum := by
      induction node with
      | nil => rfl
      | cons child rest tail =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (by split; exact ih _; exact Nat.zero_le _) tail
    omega

end Silmaril.Proofs.Formats.Dasl.ProllyRange
