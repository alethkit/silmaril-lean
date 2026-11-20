module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

private theorem run_bind {Value Result : Type} (first : Compile Value) (next : Value → Compile Result)
    (initial : List OwnedMemory.Receipt) :
    (first >>= next).run initial =
      match first.run initial with
      | .error issue => .error issue
      | .ok (value, rest) => (next value).run rest := by
  change (first.run initial >>= fun (value, rest) => (next value).run rest) = _
  cases first.run initial <;> rfl

private theorem run_pure {Value : Type} (value : Value) (initial : List OwnedMemory.Receipt) :
    (pure value : Compile Value).run initial = .ok (value, initial) := rfl

private theorem run_get (initial : List OwnedMemory.Receipt) :
    (get : Compile (List OwnedMemory.Receipt)).run initial = .ok (initial, initial) := rfl

private theorem run_set (receipts initial : List OwnedMemory.Receipt) :
    (set receipts : Compile PUnit).run initial = .ok (⟨⟩, receipts) := rfl

private theorem run_lift {Value : Type} (body : Except Endpoints.RecordLower.Issue Value)
    (initial : List OwnedMemory.Receipt) :
    (liftM body : Compile Value).run initial =
      match body with
      | .error issue => .error issue
      | .ok value => .ok (value, initial) := by
  cases body <;> rfl

theorem field_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (type : TypeOf) (value : Val) (before after : List OwnedMemory.Receipt)
    (field : Field) (objects : List Object)
    (compiled : (compileField cx output index type value).run before = .ok ((field, objects), after)) :
    field.type = type := by
  unfold compileField at compiled
  split at compiled <;>
    repeat' first
      | contradiction
      | (have same := compiled.1.1; subst field; simp_all [Field.type, Endpoints.ListLower.endpointType])
      | simp (config := {failIfUnchanged := true}) only [run_bind, run_pure, run_get,
          run_set, run_lift, Except.ok.injEq, Prod.mk.injEq] at compiled
      | split at compiled

theorem fields_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (types : List (String × TypeOf)) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field) (objects : List Object)
    (compiled : (compileFields cx output index types values).run before = .ok ((fields, objects), after)) :
    fields.map Field.type = types.map Prod.snd := by
  induction types generalizing index values before after fields objects with
  | nil =>
    cases values <;> cases compiled
    rfl
  | cons type types ih =>
    cases values with
    | nil => cases compiled
    | cons value values =>
      simp only [compileFields, run_bind, run_pure] at compiled
      split at compiled <;> try contradiction
      rename_i first middle head
      split at compiled <;> try contradiction
      rename_i rest receipts tail
      cases compiled
      simp only [List.map_cons, field_type cx output index type.2 value before middle first.1 first.2 head,
        ih (index + 1) values middle after rest.1 rest.2 tail]

theorem types_types {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (types : List TypeOf) (values : List Val)
    (before after : List OwnedMemory.Receipt) (fields : List Field) (objects : List Object)
    (compiled : (compileTypes cx output index types values).run before = .ok ((fields, objects), after)) :
    fields.map Field.type = types := by
  induction types generalizing index values before after fields objects with
  | nil =>
    cases values <;> cases compiled
    rfl
  | cons type types ih =>
    cases values with
    | nil => cases compiled
    | cons value values =>
      simp only [compileTypes, run_bind, run_pure] at compiled
      split at compiled <;> try contradiction
      rename_i first middle head
      split at compiled <;> try contradiction
      rename_i rest receipts tail
      cases compiled
      simp only [List.map_cons, field_type cx output index type value before middle first.1 first.2 head,
        ih (index + 1) values middle after rest.1 rest.2 tail]

theorem case_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (type : Option TypeOf) (payload : Option Val) (before after : List OwnedMemory.Receipt)
    (field : Option Field) (objects : List Object)
    (compiled : (compileCase cx output type payload).run before = .ok ((field, objects), after)) :
    field.map Field.type = type := by
  cases type <;> cases payload <;> simp only [compileCase, run_bind, run_pure] at compiled
  all_goals try contradiction
  case none.none => cases compiled; rfl
  case some.some type value =>
    split at compiled <;> try contradiction
    rename_i result rest plan
    cases compiled
    exact congrArg some (field_type cx output 0 type value before after result.1 result.2 plan)

theorem cases_type {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (arms : List (String × Option TypeOf)) (tag : Nat) (payload : Option Val)
    (before after : List OwnedMemory.Receipt) (field : Option Field) (objects : List Object)
    (compiled : (compileCases cx output arms tag payload).run before = .ok ((field, objects), after)) :
    arms[tag]?.map Prod.snd = some (field.map Field.type) := by
  induction arms generalizing tag with
  | nil => cases compiled
  | cons arm rest ih =>
    cases tag with
    | zero => exact congrArg some (case_type cx output arm.2 payload before after field objects compiled).symm
    | succ tag => exact ih tag compiled

theorem value_type {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Lower.Output) (field : Field) (objects : List Object)
    (compiled : compileValue cx type value receipts output = .ok (field, objects)) : field.type = type := by
  cases plan : (compileField cx output 0 type value).run receipts with
  | error issue =>
    simp only [compileValue, bind, Except.bind, plan] at compiled
    repeat' first | contradiction | split at compiled
  | ok result =>
    obtain ⟨⟨found, transfers⟩, rest⟩ := result
    simp only [compileValue, bind, Except.bind, plan] at compiled
    repeat' first
      | contradiction
      | (cases compiled; exact field_type cx output 0 type value receipts rest _ _ plan)
      | split at compiled

theorem record_types {E : CoreEngine} (cx : LiftLowerContext E) (types : List (String × TypeOf))
    (value : Val) (receipts : List OwnedMemory.Receipt) (output : Lower.Output)
    (fields : List Field) (objects : List Object)
    (compiled : compileRecord cx (.record types) value receipts output = .ok (fields, objects)) :
    fields.map Field.type = types.map Prod.snd := by
  cases options : Lower.checkOptions cx (.record types) output with
  | error issue => simp [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
  | ok accepted =>
    cases value <;> simp only [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
    all_goals try contradiction
    case record values =>
      cases plan : (compileFields cx output 0 types values).run receipts with
      | error issue => rw [plan] at compiled; contradiction
      | ok result =>
        obtain ⟨⟨found, transfers⟩, rest⟩ := result
        simp only [plan, pure, Except.pure] at compiled
        repeat' first
          | contradiction
          | (cases compiled; exact fields_types cx output 0 types values receipts rest _ _ plan)
          | split at compiled

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordTypes
