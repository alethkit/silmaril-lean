module

import Silmaril.Semantics.Relational.All

/-! Database-backed query observations through the public relational interface. -/

namespace Silmaril.Relational.IntegrationExamples

open Database UB

private inductive Name where
  | missing | empty | samples

private abbrev Schema := PositionalSchema Unit
private abbrev Cell (_ : Unit) := Nat
private abbrev TypedTable (schema : Schema) := Table schema.kind Cell
private abbrev AlignedTable (schema : Schema) := AlignedColumns schema.kind Cell

private def oneColumn : Schema := ⟨1, fun _ => ()⟩
private def zeroColumns : Schema := ⟨0, Fin.elim0⟩

private def sampleCatalog : Catalog Name Schema
  | .missing => none
  | .empty => some zeroColumns
  | .samples => some oneColumn

private def sampleDB : Dependent Name TypedTable :=
  ⟨sampleCatalog, fun
    | .missing => PUnit.unit
    | .empty => []
    | .samples => [fun _ => 7, fun _ => 3, fun _ => 7]⟩

private def eraseRows (schema : Schema) (table : TypedTable schema) : List (List Nat) :=
  schema.eraseTable (fun _ cell => cell) table

private inductive ReadError where
  | missing (name : Name)
  | unsupported

private abbrev Answer := Except ReadError (Output (List Nat) Unit Schema Name)

/-- Use the source name as metadata and preserve the stored row sequence. -/
private def readRows (db : Packed Name TypedTable) (name : Name) : Answer :=
  match db name with
  | none => .error (.missing name)
  | some ⟨schema, table⟩ => .ok (.rows ⟨schema, name⟩ (.ordered (eraseRows schema table)))

example : readRows sampleDB.pack .missing = .error (.missing .missing) := rfl
example : readRows sampleDB.pack .empty = .ok (.rows ⟨zeroColumns, .empty⟩ (.ordered [])) := rfl
example : readRows sampleDB.pack .samples =
    .ok (.rows ⟨oneColumn, .samples⟩ (.ordered [[7], [3], [7]])) := rfl

example (db : Dependent Name TypedTable) (name : Name) :
    readRows db.pack.unpack.pack name = readRows db.pack name := by rw [unpack_pack]

private def encodeAligned (schema : Schema) (table : TypedTable schema) : Sigma AlignedTable :=
  ⟨schema, AlignedColumns.ofRows table⟩

private def decodeAligned (entry : Sigma AlignedTable) : Sigma TypedTable :=
  ⟨entry.fst, entry.snd.toRows⟩

private theorem decode_encode :
    Function.LeftInverse decodeAligned (fun entry : Sigma TypedTable =>
      encodeAligned entry.fst entry.snd) := by
  rintro ⟨schema, table⟩
  exact congrArg (Sigma.mk schema) (AlignedColumns.toRows_ofRows table)

private def roundTrip (db : Packed Name TypedTable) : Packed Name TypedTable :=
  Partial.map decodeAligned (Packed.erase encodeAligned db)

private theorem roundTrip_eq (db : Packed Name TypedTable) : roundTrip db = db := by
  funext name
  change ((db name).map (fun entry => encodeAligned entry.fst entry.snd)).map decodeAligned = db name
  cases db name with
  | none => rfl
  | some entry => exact congrArg some (decode_encode entry)

example : readRows (roundTrip sampleDB.pack) .samples =
    .ok (.rows ⟨oneColumn, .samples⟩ (.ordered [[7], [3], [7]])) := by rw [roundTrip_eq]; rfl

-- Dropping the schema retains absence, but two present empty schemas collide.
example : Packed.erase eraseRows sampleDB.pack .missing = none := rfl
example : Packed.erase eraseRows sampleDB.pack .empty = some [] := rfl

example : ¬ Recoverable eraseRows (Packed.erase eraseRows sampleDB.pack) := by
  rintro recoverable
  obtain ⟨_, _, unique⟩ := recoverable .empty [] rfl
  have same : (⟨zeroColumns, []⟩ : Sigma TypedTable) = ⟨oneColumn, []⟩ :=
    (unique ⟨zeroColumns, []⟩ rfl).trans (unique ⟨oneColumn, []⟩ rfl).symm
  have width := congrArg (fun entry => entry.fst.width) same
  cases width

-- Keeping the schema with the aligned payload makes the packed preimage unique.
private theorem aligned_recoverable (db : Packed Name TypedTable) :
    Recoverable encodeAligned (Packed.erase encodeAligned db) :=
  recoverable_of_injective encodeAligned db decode_encode.injective

example (db : Packed Name TypedTable) (name : Name) :
    readRows (recover encodeAligned (Packed.erase encodeAligned db) (aligned_recoverable db)) name =
      readRows db name := by rw [recover_erase]

private abbrev DB := Packed Name TypedTable

private def readSpec : QueryRel DB Name Answer := QueryRel.ofTotal readRows
private def alignedRead (db : DB) (name : Name) : Answer := readRows (roundTrip db) name

example : (QueryRel.ofTotal alignedRead).Equivalent readSpec := by
  apply QueryRel.equivalent_iff_eq.mpr
  funext db name answer
  change (readRows (roundTrip db) name = answer) = (readRows db name = answer)
  rw [roundTrip_eq]

private def embed : Name ↪ Option Name := ⟨some, fun _ _ h => Option.some.inj h⟩

private def wideRead (db : DB) : Option Name → Answer
  | some name => alignedRead db name
  | none => .error .unsupported

private def spec : ExplicitQuery DB Name Answer Unit := ExplicitQuery.ofQueryRel readSpec
private def impl : ExplicitQuery DB (Option Name) Answer Unit :=
  ExplicitQuery.ofQueryRel (QueryRel.ofTotal wideRead)

private theorem restrict_impl : impl.restrict embed = spec := by
  funext db name
  change spec (roundTrip db) name = spec db name
  rw [roundTrip_eq]

example : impl.AgreesOn (fun _ query => ∃ name, embed name = query) (spec.extendUB embed ()) := by
  apply (ExplicitQuery.agreesOn_image_iff embed _ _).mpr
  rw [restrict_impl, ExplicitQuery.restrict_extendUB]

-- The ordinary missing-table error is still a safe outcome inside the fragment.
example : (impl sampleDB.pack (embed .missing)).Safe ∧
    impl.forget sampleDB.pack (embed .missing) (.error (.missing .missing)) := ⟨rfl, rfl⟩

example : impl.collapse ≤ (spec.extendUB embed ()).collapse := by
  rw [ExplicitQuery.collapse_extendUB]
  apply (CatastrophicQuery.le_extendUB_iff embed _ _).mpr
  exact fun db name => (congrArg Explicit.collapse (congrFun (congrFun restrict_impl db) name)).le

-- Outside the image, an ordinary error violates the explicit empty result set.
example : ¬ impl ≤ spec.extendUB embed () := by
  intro refines
  have outside : ¬ ∃ name, embed name = none := by simp [embed]
  have allowed :=
    ((ExplicitQuery.le_extendUB_iff embed () impl spec).mp refines).2 sampleDB.pack none outside
  have seen : (.error .unsupported : Answer) ∈ (impl sampleDB.pack none).results := rfl
  exact allowed.1 seen

end Silmaril.Relational.IntegrationExamples
