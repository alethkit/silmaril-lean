module

public import Silmaril.Formats.Sqlite.Record.Defs
import Silmaril.Formats.Sqlite.Varint.Thms

public section

namespace Silmaril.Proofs.Formats.Sqlite.Record.Header

open Silmaril.Formats.Sqlite Silmaril.Formats.Sqlite.Record

private theorem header_done (source : File.View) (stop fuel : Nat) :
    headerAux? source stop fuel stop = some [] := by
  cases fuel <;> simp [headerAux?]

theorem headerAux?_exact_fuel (source : File.View) (stop budget offset : Nat) {codes : List Nat}
    (parsed : headerAux? source stop budget offset = some codes) :
    codes.length ≤ budget ∧ offset + codes.length ≤ stop ∧
    ∀ fuel, headerAux? source stop fuel offset =
      if codes.length ≤ fuel then some codes else none := by
  induction budget generalizing offset codes with
  | zero =>
    by_cases done : offset = stop
    · subst offset
      rw [header_done] at parsed
      cases parsed
      simp [header_done]
    · simp [headerAux?, done] at parsed
  | succ budget ih =>
    by_cases done : offset = stop
    · subst offset
      rw [header_done] at parsed
      cases parsed
      simp [header_done]
    · by_cases past : offset > stop
      · simp [headerAux?, done, past] at parsed
      · simp only [headerAux?, beq_iff_eq, done, ite_false, past] at parsed
        obtain ⟨⟨code, next⟩, read, parsed⟩ := Option.bind_eq_some_iff.mp parsed
        dsimp only at parsed
        split at parsed
        · cases parsed
        · rename_i bound
          obtain ⟨tail, rest, parsed⟩ := Option.bind_eq_some_iff.mp parsed
          cases parsed
          obtain ⟨count, consumed, stable⟩ := ih next rest
          have progress : offset < next :=
            (Varint.readAux?_progress source 9 offset 0 code next read).1
          refine ⟨by simpa using count, by simp only [List.length_cons]; omega, ?_⟩
          intro fuel
          cases fuel with
          | zero => simp [headerAux?, done]
          | succ fuel =>
            simp only [headerAux?, beq_iff_eq, done, ite_false, past, read]
            change (if stop < next then none else
              (headerAux? source stop fuel next).bind fun codes => some (code :: codes)) = _
            rw [ite_eq_right bound, stable]
            by_cases enough : tail.length ≤ fuel
            <;> simp [enough]

theorem headerAux?_fuel_irrel (source : File.View) (stop offset left right : Nat)
    (leftEnough : stop - offset ≤ left) (rightEnough : stop - offset ≤ right) :
    headerAux? source stop left offset = headerAux? source stop right offset := by
  cases lhs : headerAux? source stop left offset with
  | some codes =>
    obtain ⟨_, consumed, stable⟩ := headerAux?_exact_fuel source stop left offset lhs
    have enough : codes.length ≤ right := by omega
    simp [stable right, enough]
  | none =>
    cases rhs : headerAux? source stop right offset with
    | none => rfl
    | some codes =>
      obtain ⟨_, consumed, stable⟩ := headerAux?_exact_fuel source stop right offset rhs
      have enough : codes.length ≤ left := by omega
      simp [stable left, enough] at lhs

end Silmaril.Proofs.Formats.Sqlite.Record.Header
