module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.MemorySum

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (TypeOf)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower (Output)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Internal (runField)

variable {E : CoreEngine} {World : Type}

private def armStore (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) : Option Field → P E World Unit
  | none => pure ()
  | some field => store limits quirks cx field.value field.type ptr

private theorem rejoin (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag index ptr : Nat) (arm : Option Field)
    (child : ∀ field address, arm = some field →
      runField limits quirks cx authority width field 0 (.memory address) =
        Except.ok <$> store limits quirks cx field.value field.type address) :
    runField limits quirks cx authority width (.sum type arms tag arm) index (.memory ptr) =
      (do
        let address ← storeVariantHead cx arms.length (maxCaseAlignment (arms.map (layoutOption width))) tag ptr
        Except.ok <$> armStore limits quirks cx address arm) := by
  cases arm with
  | none =>
    simp [runField, armStore]
    rfl
  | some field =>
    rw [runField]
    dsimp only [Output.Result]
    simp only [armStore, child _ _ rfl, ← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
    congr 1

private theorem caseStore_at (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) (payload : Option Val) (cases : List (String × Option TypeOf)) (tag : Nat)
    (selected : Option TypeOf) (found : (cases.map Prod.snd)[tag]? = some selected) :
    (storeCase limits quirks cx tag payload cases ptr : P E World _) =
      storeOpt limits quirks cx payload selected ptr := by
  induction cases generalizing tag with
  | nil => simp at found
  | cons entry rest ih =>
    cases tag with
    | zero =>
      have eq : entry.2 = selected := by simpa using found
      cases entry
      simpa [storeCase] using congrArg (fun t => storeOpt limits quirks cx payload t ptr) eq
    | succ tag =>
      rw [storeCase]
      exact ih tag (by simpa using found)

private theorem caseLayouts (width : AddrType) (cases : List (String × Option TypeOf)) :
    (cases.map Prod.snd).map (layoutOption width) = layoutCases width cases := by
  induction cases with
  | nil => simp [layoutCases]
  | cons entry rest ih =>
    cases entry
    simp [layoutCases, ih]

private theorem armStore_matches (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) {arm : Option Field} {type : Option TypeOf} (certificate : Field.ArmMatches arm type) :
    (armStore limits quirks cx ptr arm : P E World _) =
      storeOpt limits quirks cx (Field.armValue arm) type ptr := by
  cases certificate with
  | none => simp [armStore, storeOpt]
  | some layout => simp [armStore, storeOpt, Field.armValue, layout.type_eq]

theorem sum_rejoin (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (type : TypeOf) (arms : List (Option TypeOf)) (tag index ptr : Nat)
    (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type)
    (child : ∀ width field address, arm = some field →
      runField limits quirks cx authority width field 0 (.memory address) =
        Except.ok <$> store limits quirks cx field.value field.type address) :
    (do
      let width ← ptrType cx
      runField limits quirks cx authority width (.sum type arms tag arm) index (.memory ptr)) =
      Except.ok <$> store limits quirks cx (.variant tag (Field.armValue arm)) type ptr := by
  dsimp only [Output.Result]
  cases layout with
  | variant found certificate =>
    rename_i types selected
    rw [store]
    simp only [← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext width
    rw [rejoin limits quirks cx authority width _ _ tag index ptr arm (child width)]
    dsimp only [Output.Result]
    simp only [List.length_map, caseLayouts, caseStore_at _ _ _ _ _ _ _ _ found,
      armStore_matches _ _ _ _ certificate, ← bind_pure_comp, Prog.bind_eq]
  | optionNone =>
    rw [store]
    simp only [← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext width
    rw [rejoin limits quirks cx authority width _ _ _ index ptr _ (child width)]
    dsimp only [Output.Result]
    simp [armStore, layoutOption, ← bind_pure_comp]
  | optionSome certificate =>
    rw [store]
    simp only [Field.armValue, ← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext width
    rw [rejoin limits quirks cx authority width _ _ _ index ptr _ (child width)]
    dsimp only [Output.Result]
    simp [armStore, layoutOption, certificate.type_eq, ← bind_pure_comp]
  | resultOk certificate =>
    rw [store]
    simp only [← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext width
    rw [rejoin limits quirks cx authority width _ _ _ index ptr _ (child width)]
    dsimp only [Output.Result]
    simp [armStore_matches _ _ _ _ certificate, ← bind_pure_comp]
  | resultError certificate =>
    rw [store]
    simp only [← bind_pure_comp, Prog.bind_eq, Prog.bind_assoc]
    congr 1
    funext width
    rw [rejoin limits quirks cx authority width _ _ _ index ptr _ (child width)]
    dsimp only [Output.Result]
    simp [armStore_matches _ _ _ _ certificate, ← bind_pure_comp]

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.MemorySum
