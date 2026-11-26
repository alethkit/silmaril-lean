module

public import Silmaril.Relational.Database.Thms

@[expose] public section

namespace Silmaril.Relational.Database.Examples

def Cell : Bool → Type
  | false => Nat
  | true => Bool

abbrev TypedTable (schema : PositionalSchema Bool) := Table schema.kind Cell

def encode : (k : Bool) → Cell k → Nat
  | false, n => n
  | true, b => if (show Bool from b) then 7 else 0

def erase (schema : PositionalSchema Bool) : TypedTable schema → List (List Nat) :=
  schema.eraseTable encode

private def zeroWidth : PositionalSchema Bool := ⟨0, Fin.elim0⟩
private def naturals : PositionalSchema Bool := ⟨1, fun _ => false⟩
private def booleans : PositionalSchema Bool := ⟨1, fun _ => true⟩

private def single (schema : PositionalSchema Bool) (table : TypedTable schema) : Packed Unit TypedTable :=
  fun () => some ⟨schema, table⟩

/-- Empty tables of different widths erase to the same occupied entry. -/
theorem empty_tables_lose_schema :
    ∃ a b : Packed Unit TypedTable, a ≠ b ∧ Packed.erase erase a = Packed.erase erase b := by
  refine ⟨single zeroWidth [], single naturals [], ?_, rfl⟩
  intro equal
  have widths := congrArg (fun db => (Packed.catalog db ()).map PositionalSchema.width) equal
  change some 0 = some 1 at widths
  cases widths

/-- The two occupied entries each erase to the single row `[7]`, despite different cell kinds. -/
theorem nonempty_tables_can_be_ambiguous :
    ∃ a b : Packed Unit TypedTable, a ≠ b ∧
      Packed.erase erase a () = some [[7]] ∧ Packed.erase erase b () = some [[7]] := by
  refine ⟨single naturals [fun _ => (7 : Nat)], single booleans [fun _ => true], ?_, rfl, rfl⟩
  intro equal
  have kinds := congrArg (fun db => (Packed.catalog db ()).map fun s => List.ofFn s.kind) equal
  change some [false] = some [true] at kinds
  cases kinds

private def numbers : Packed Bool (fun _ : Unit => Nat)
  | false => none
  | true => some ⟨(), 9⟩

private def numberValue (_ : Unit) (n : Nat) : Nat := n

private theorem numberValue_injective :
    Function.Injective (fun entry : Σ _ : Unit, Nat => numberValue entry.fst entry.snd) := by
  rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ equal
  exact congrArg (fun n : Nat => (⟨(), n⟩ : Σ _ : Unit, Nat)) equal

private theorem numbers_recoverable : Recoverable numberValue (Packed.erase numberValue numbers) :=
  recoverable_of_injective numberValue numbers numberValue_injective

example : Over.lookup (Packed.unpack numbers).snd true rfl = 9 := rfl

example : recover numberValue (Packed.erase numberValue numbers) numbers_recoverable true =
    some ⟨(), 9⟩ := by rw [recover_erase]; rfl

example : recover numberValue (Packed.erase numberValue numbers) numbers_recoverable false =
    none := by rw [recover_erase]; rfl

example : FiniteSupport numbers :=
  Finite.of_injective (fun name : Support numbers => name.val) Subtype.val_injective

end Silmaril.Relational.Database.Examples
