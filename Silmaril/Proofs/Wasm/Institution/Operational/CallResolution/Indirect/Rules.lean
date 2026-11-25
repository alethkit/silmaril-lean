module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs

open CallContinuation.OuterCall.Ranked.Graph (Program)
open Execution.Runtime (Frame)

theorem resolve_iff {site : Site} {program : Program} {selector : BitVec 32} {out : Outcome} :
    site.resolve program selector = some out ↔ Resolution site program selector out := by
  constructor
  · unfold Site.resolve
    split
    next entry => rintro ⟨rfl⟩; exact .bounds entry
    next entry => rintro ⟨rfl⟩; exact .null entry
    next addr entry =>
      cases found : program.lookup addr with
      | none => simp
      | some fn =>
        change some (if fn.declaration.type = site.signature then .resolved addr else .mismatch addr) = some out → _
        by_cases same : fn.declaration.type = site.signature
        · simp only [ite_eq_left same, Option.some.injEq]
          rintro rfl
          exact .resolved entry found same
        · simp only [ite_eq_right same, Option.some.injEq]
          rintro rfl
          exact .mismatch entry found same
  · intro result
    cases result <;> simp [Site.resolve, *]

theorem resolve_total {site : Site} {program : Program} {caller : Frame} {selector : BitVec 32}
    (checked : site.check program caller = true) : ∃ out, site.resolve program selector = some out := by
  cases entry : site.table.refs[selector.toNat]? with
  | none => exact ⟨.bounds, by simp [Site.resolve, entry]⟩
  | some entryValue =>
    cases entryValue with
    | none => exact ⟨.null, by simp [Site.resolve, entry]⟩
    | some addr =>
      have members := (Bool.and_eq_true_iff.mp checked).2
      have declared := List.all_eq_true.mp members _ (List.mem_of_getElem? entry)
      cases found : program.lookup addr with
      | none => simp [found] at declared
      | some fn => simp [Site.resolve, entry, found]

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs
