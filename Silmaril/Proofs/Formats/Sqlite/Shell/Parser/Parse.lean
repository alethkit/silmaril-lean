module

public import Silmaril.Formats.Sqlite.Shell.Defs

public section

namespace Silmaril.Proofs.Formats.Sqlite.Shell.Parser

open Silmaril.Formats.Sqlite.Shell

private theorem selection {tokens : List String} {columns : List Column}
    (parsed : selectColumns? tokens = some columns) :
    columns = [.id, .amount] ∨ columns = [.amount, .id] ∨
    columns = [.id] ∨ columns = [.amount] := by
  unfold selectColumns? at parsed
  split at parsed <;> simp_all

theorem parse?_projection_and_offset {sql : String} {query : Query}
    (parsed : parse? sql = some query) :
    (query.columns = [.id, .amount] ∨ query.columns = [.amount, .id] ∨
      query.columns = [.id] ∨ query.columns = [.amount]) ∧
    (query.limit = none → query.offset = 0) := by
  simp only [parse?, pure, bind, Option.bind_some] at parsed
  split at parsed
  next terms words =>
    split at parsed
    next tail rest =>
      obtain ⟨columns, selected, parsed⟩ := Option.bind_eq_some_iff.mp parsed
      have valid := selection selected
      split at parsed
      case' h_1 =>
        obtain ⟨_, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
      all_goals
        split at parsed
        · cases parsed
          exact ⟨valid, fun _ => rfl⟩
        · obtain ⟨count, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
          cases parsed
          exact ⟨valid, by simp⟩
        · obtain ⟨count, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
          obtain ⟨offset, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
          cases parsed
          exact ⟨valid, by simp⟩
        · cases parsed
    next => cases parsed
  next => cases parsed

end Silmaril.Proofs.Formats.Sqlite.Shell.Parser
