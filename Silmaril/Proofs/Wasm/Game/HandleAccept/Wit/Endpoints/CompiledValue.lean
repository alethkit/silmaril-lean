module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CompiledValue

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit Silmaril.Wasm.Game.HandleAccept.Wit.Stored
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

private abbrev Receipt := OwnedMemory.Receipt
private abbrev Issue := Endpoints.RecordLower.Issue

private def Produces {Shape : Type} (compile : Compile Shape) (spec : Shape → Prop) : Prop :=
  ∀ before after shape, compile.run before = .ok (shape, after) → spec shape

private theorem run_bind {Value Result : Type} (first : Compile Value) (next : Value → Compile Result)
    (before : List Receipt) :
    (first >>= next).run before = match first.run before with
    | .error issue => .error issue
    | .ok (value, rest) => (next value).run rest := by
  change (first.run before >>= fun (value, rest) => (next value).run rest) = _
  cases first.run before <;> rfl

private theorem bind_spec {Value Result : Type} {first : Compile Value} {next : Value → Compile Result}
    {initial : Value → Prop} {spec : Result → Prop} (firstSpec : Produces first initial)
    (nextSpec : ∀ value, initial value → Produces (next value) spec) : Produces (first >>= next) spec := by
  intro before after result run
  rw [run_bind] at run
  split at run
  · contradiction
  · rename_i value middle entered
    exact nextSpec value (firstSpec _ _ _ entered) _ _ _ run

private theorem pure_spec {Shape : Type} (shape : Shape) {spec : Shape → Prop} (holds : spec shape) :
    Produces (pure shape) spec := by
  intro before after found run
  rw [← (Prod.mk.inj (Except.ok.inj run)).1]
  exact holds

private theorem error_spec {Shape : Type} (issue : Issue) (spec : Shape → Prop) :
    Produces (throw issue) spec := by
  intro before after found run
  contradiction

private theorem wrap_spec {Inner Outer : Type} {compile : Compile Inner} {inner : Inner → Prop}
    (wrap : Inner → Outer) {spec : Outer → Prop} (preserves : ∀ value, inner value → spec (wrap value))
    (produces : Produces compile inner) : Produces (do let value ← compile; pure (wrap value)) spec :=
  bind_spec produces fun value holds => pure_spec _ (preserves value holds)

private theorem cons_spec {head : Compile Field} {tail : Compile (List Field)} {value : Val}
    {values : List Val} (headSpec : Produces head (fun field => field.value = value))
    (tailSpec : Produces tail (fun fields => Field.values fields = values)) :
    Produces (do let field ← head; let fields ← tail; pure (field :: fields))
      (fun fields => Field.values fields = value :: values) :=
  bind_spec headSpec fun field equal => wrap_spec (List.cons field)
    (fun fields rest => by simp only [Field.values, equal, rest]) tailSpec

private theorem mapIssue_spec {Shape : Type} {compile : Compile Shape} {spec : Shape → Prop}
    (produces : Produces compile spec) (map : Issue → Issue) : Produces (compile.mapIssue map) spec := by
  intro before after shape run
  change (compile.run before).mapError map = _ at run
  cases entered : compile.run before with
  | error issue => rw [entered] at run; contradiction
  | ok result => rw [entered] at run; exact produces _ _ _ (entered.trans run)

private theorem check_spec {Shape : Type} (type : TypeOf) (value : Val) (map : Stored.Issue → Issue)
    (next : Stored.Payload type → Compile Shape) {spec : Shape → Prop}
    (produces : ∀ payload, payload.val = value → Produces (next payload) spec) :
    Produces (liftM ((Stored.checkValue type value).mapError map) >>= next) spec := by
  unfold Stored.checkValue
  split
  · exact produces _ rfl
  · intro before after shape run; contradiction

private theorem entries_spec (compile : Nat → Val → Compile Field)
    (element : ∀ index value, Produces (compile index value) (fun field => field.value = value)) :
    ∀ (values : List Val) (start : Nat),
      Produces ((values.zipIdx start).mapM (fun (value, index) => compile index value))
        (fun fields => Field.values fields = values) := by
  intro values
  induction values with
  | nil => intro start; exact pure_spec [] rfl
  | cons value values ih =>
    intro start
    simp only [List.zipIdx_cons, List.mapM_cons]
    exact cons_spec (element start value) (ih (start + 1))

private theorem compileEntries_spec (compile : Nat → Val → Compile Field) (values : List Val)
    (element : ∀ index value, Produces (compile index value) (fun field => field.value = value)) :
    Produces (Internal.compileEntries compile values) (fun fields => Field.values fields = values) :=
  entries_spec compile element values 0

private theorem leaf_spec (index : Nat) (type : TypeOf) (value : Val) :
    Produces (Internal.compileLeaf index type value) (fun field => field.value = value) := by
  unfold Internal.compileLeaf
  apply check_spec
  intro payload equal
  split <;> try exact pure_spec _ equal
  split
  · exact pure_spec _ equal
  · exact error_spec _ _

private theorem owner_spec {E : CoreEngine} {cx : LiftLowerContext E} {output : Lower.Output}
    (index : Nat) (resource : RtId) (representation : Nat) :
    Produces (Internal.compileField cx output index (.own resource) (.own representation))
      (fun field => field.value = .own representation) := by
  intro before after field compiled
  cases before with
  | nil => cases compiled
  | cons receipt rest =>
    have read : (get : Compile (List Receipt)).run (receipt :: rest) =
        .ok (receipt :: rest, receipt :: rest) := rfl
    simp only [Internal.compileField, run_bind, read] at compiled
    split at compiled
    · contradiction
    · rename_i accepted
      cases compiled
      simp only [Field.value, Val.own.injEq]
      by_contra different
      simp [different] at accepted

section
variable {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)

mutual
private theorem field_spec (index : Nat) (type : TypeOf) (value : Val) :
    Produces (Internal.compileField cx output index type value) (fun field => field.value = value) := by
  cases type <;> try exact leaf_spec index _ value
  case record types =>
    simp only [Internal.compileField]
    split
    · rename_i values
      exact wrap_spec (Field.aggregate _) (fun _ equal => congrArg Val.record equal)
        (mapIssue_spec (fields_spec 0 types values) _)
    · exact error_spec _ _
  case tuple types =>
    simp only [Internal.compileField]
    split
    · rename_i values
      exact wrap_spec (Field.aggregate _) (fun _ equal => congrArg Val.record equal)
        (mapIssue_spec (types_spec 0 types values) _)
    · exact error_spec _ _
  case fixedList type length =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i values
        split
        · exact error_spec _ _
        · exact wrap_spec (Field.fixed type length) (fun _ equal => congrArg Val.list equal)
            (mapIssue_spec (compileEntries_spec _ values (fun pos child => field_spec pos type child)) _)
      · exact error_spec _ _
  case list type =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i values
        exact wrap_spec (Field.dynamic (.list type) type) (fun _ equal => congrArg Val.list equal)
          (mapIssue_spec (compileEntries_spec _ values (fun pos child => field_spec pos type child)) _)
      · exact error_spec _ _
  case map key type =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i values
        refine wrap_spec (Field.dynamic (.map key type) _) (fun _ equal => congrArg Val.list equal)
          (mapIssue_spec (compileEntries_spec _ values ?_) _)
        intro pos item
        split
        · rename_i keyValue payload
          apply check_spec
          intro checked sameKey
          exact wrap_spec (fun field => Field.aggregate _ [.data _ checked, field])
            (fun field equal => by simp only [Field.value, Field.values, sameKey, equal])
            (mapIssue_spec (field_spec 1 type payload) _)
        · exact error_spec _ _
      · exact error_spec _ _
  case option type =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · exact pure_spec _ rfl
      · rename_i child
        exact wrap_spec (fun field => Field.sum (.option type) [none, some type] 1 (some field))
          (fun _ equal => congrArg (fun child => Val.variant 1 (some child)) equal)
          (mapIssue_spec (field_spec 0 type child) _)
      · exact error_spec _ _
  case variant arms =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i tag payload
        exact wrap_spec (Field.sum (.variant arms) (arms.map Prod.snd) tag)
          (fun _ equal => congrArg (Val.variant tag) equal) (mapIssue_spec (cases_spec arms tag payload) _)
      · exact error_spec _ _
  case result success failure =>
    simp only [Internal.compileField]
    split
    · exact error_spec _ _
    · split
      · rename_i payload
        exact wrap_spec (Field.sum (.result success failure) [success, failure] 0)
          (fun _ equal => congrArg (Val.variant 0) equal) (mapIssue_spec (case_spec success payload) _)
      · rename_i payload
        exact wrap_spec (Field.sum (.result success failure) [success, failure] 1)
          (fun _ equal => congrArg (Val.variant 1) equal) (mapIssue_spec (case_spec failure payload) _)
      · exact error_spec _ _
  case own resource =>
    cases value <;> first | exact owner_spec index resource _ | exact leaf_spec index _ _
termination_by structural type

private theorem fields_spec (index : Nat) (types : List (String × TypeOf)) (values : List Val) :
    Produces (Internal.compileFields cx output index types values) (fun fields => Field.values fields = values) := by
  cases types with
  | nil => cases values <;> first | exact pure_spec _ rfl | exact error_spec _ _
  | cons type types =>
    cases values with
    | nil => exact error_spec _ _
    | cons value values =>
      exact cons_spec (field_spec index type.2 value) (fields_spec (index + 1) types values)
termination_by structural types

private theorem types_spec (index : Nat) (types : List TypeOf) (values : List Val) :
    Produces (Internal.compileTypes cx output index types values) (fun fields => Field.values fields = values) := by
  cases types with
  | nil => cases values <;> first | exact pure_spec _ rfl | exact error_spec _ _
  | cons type types =>
    cases values with
    | nil => exact error_spec _ _
    | cons value values =>
      exact cons_spec (field_spec index type value) (types_spec (index + 1) types values)
termination_by structural types

private theorem cases_spec (arms : List (String × Option TypeOf)) (tag : Nat) (payload : Option Val) :
    Produces (Internal.compileCases cx output arms tag payload) (fun field => Field.armValue field = payload) := by
  cases arms with
  | nil => exact error_spec _ _
  | cons arm arms =>
    cases tag with
    | zero => exact case_spec arm.2 payload
    | succ tag => exact cases_spec arms tag payload
termination_by structural arms

private theorem case_spec (type : Option TypeOf) (payload : Option Val) :
    Produces (Internal.compileCase cx output type payload) (fun field => Field.armValue field = payload) := by
  cases type with
  | none => cases payload <;> first | exact pure_spec _ rfl | exact error_spec _ _
  | some type =>
    cases payload with
    | none => exact error_spec _ _
    | some value => exact wrap_spec some (fun _ equal => congrArg some equal) (field_spec 0 type value)
termination_by structural type
end

end

private theorem field {E : CoreEngine} (cx : LiftLowerContext E) (output : Lower.Output)
    (index : Nat) (type : TypeOf) (value : Val) (field : Field) (objects : List Object)
    (before after : List OwnedMemory.Receipt)
    (compiled : (compileField cx output index type value).run before = .ok ((field, objects), after)) :
    field.value = value := by
  change ((Internal.compileField cx output index type value).run before).map _ = _ at compiled
  cases step : (Internal.compileField cx output index type value).run before with
  | error issue => rw [step] at compiled; contradiction
  | ok result =>
    obtain ⟨found, rest⟩ := result
    rw [step] at compiled
    cases compiled
    exact field_spec cx output index type value _ _ _ step

theorem value {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf) (value : Val)
    (receipts : List OwnedMemory.Receipt) (output : Lower.Output) (shape : Field) (objects : List Object)
    (compiled : compileValue cx type value receipts output = .ok (shape, objects)) : shape.value = value := by
  cases run : (compileField cx output 0 type value).run receipts with
  | error issue =>
    simp only [compileValue, bind, Except.bind, run] at compiled
    repeat' first | contradiction | split at compiled
  | ok result =>
    obtain ⟨⟨found, plan⟩, rest⟩ := result
    cases rest <;> simp only [compileValue, bind, Except.bind, run, List.isEmpty, Bool.not_true,
      Bool.not_false, ite_true] at compiled
    <;> repeat' first
      | contradiction
      | (cases compiled; exact field cx output 0 type value _ _ _ _ run)
      | split at compiled

theorem record {E : CoreEngine} (cx : LiftLowerContext E) (types : List (String × TypeOf))
    (value : Val) (receipts : List OwnedMemory.Receipt) (output : Lower.Output)
    (fields : List Field) (objects : List Object)
    (compiled : compileRecord cx (.record types) value receipts output = .ok (fields, objects)) :
    .record (Field.values fields) = value := by
  cases options : Lower.checkOptions cx (.record types) output with
  | error issue => simp [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
  | ok accepted =>
    cases value <;> simp only [compileRecord, bind, Except.bind, options, Except.mapError] at compiled
    all_goals try contradiction
    case record values =>
      cases run : (compileFields cx output 0 types values).run receipts with
      | error issue => rw [run] at compiled; contradiction
      | ok result =>
        obtain ⟨⟨found, plan⟩, rest⟩ := result
        cases rest <;> simp only [run, pure, Except.pure, List.isEmpty, Bool.not_true,
          Bool.not_false, ite_true] at compiled
        · cases compiled
          change ((Internal.compileFields cx output 0 types values).run receipts).map _ = _ at run
          cases step : (Internal.compileFields cx output 0 types values).run receipts with
          | error issue => rw [step] at run; contradiction
          | ok result =>
            obtain ⟨fields, rest⟩ := result
            rw [step] at run
            cases run
            exact congrArg Val.record (fields_spec cx output 0 types values _ _ _ step)
        · contradiction

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CompiledValue
