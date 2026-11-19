module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.List.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element)

inductive Issue where
  | preflight (issue : Lower.Issue)
  | notRecord
  | unsupportedField (index : Nat)
  | field (index : Nat) (issue : ListLower.Issue)
  | nested (index : Nat) (issue : Issue)
  deriving DecidableEq, Repr

inductive Field where
  | data (type : TypeOf) (payload : Payload type)
  | endpoint (channel : Channel) (element : Element) (id : EndId)
  | context (id : ErrCtxId)
  | aggregate (type : TypeOf) (fields : List Field)
  | fixed (element : TypeOf) (length : Nat) (entries : List Field)
  | list (element : TypeOf) (entries : List Field) (plan : List Lower.Object)
  | sum (type : TypeOf) (arms : List (Option TypeOf)) (tag : Nat) (field : Option Field)

def Field.type : Field → TypeOf
  | .data type _ => type
  | .endpoint channel element _ => ListLower.endpointType channel element
  | .context _ => .errorContext
  | .aggregate type _ => type
  | .fixed element length _ => .fixedList element length
  | .list element _ _ => .list element
  | .sum type _ _ _ => type

namespace Internal

mutual
def supportedField : TypeOf → Bool
  | .record fields => supportedFields fields
  | .tuple types => supportedTypes types
  | .option type => supportedField type
  | .list type | .fixedList type _ => supportedField type
  | .variant cases => supportedCases cases
  | .result ok error => supportedCase ok && supportedCase error
  | .future _ | .stream _ | .errorContext => true
  | type => (Stored.Lower.checkSchema type).isOk
termination_by structural type => type

def supportedFields : List (String × TypeOf) → Bool
  | [] => true
  | (_, type) :: rest => supportedField type && supportedFields rest
termination_by structural fields => fields

def supportedTypes : List TypeOf → Bool
  | [] => true
  | type :: rest => supportedField type && supportedTypes rest
termination_by structural types => types

def supportedCases : List (String × Option TypeOf) → Bool
  | [] => true
  | (_, type) :: rest => supportedCase type && supportedCases rest
termination_by structural cases => cases

def supportedCase : Option TypeOf → Bool
  | none => true
  | some type => supportedField type
termination_by structural type => type
end

end Internal

def compileItems (compile : Nat → Val → Except Issue (Field × List Lower.Object))
    (values : List Val) : Except Issue (List Field × List Lower.Object) := do
  let items ← values.zipIdx.mapM (fun (value, index) => compile index value)
  return (items.map Prod.fst, items.flatMap Prod.snd)

mutual
def compileField {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) : (type : TypeOf) → Val → Except Issue (Field × List Lower.Object)
  | .record types, value => do
    let .record values := value | throw (.preflight .decodedType)
    let (fields, plan) ← (compileFields cx output 0 types values).mapError (.nested index)
    return (.aggregate (.record types) fields, plan)
  | .tuple types, value => do
    let .record values := value | throw (.preflight .decodedType)
    let (fields, plan) ← (compileTypes cx output 0 types values).mapError (.nested index)
    return (.aggregate (.tuple types) fields, plan)
  | .fixedList type length, value => do
    if !Internal.supportedField type then throw (.unsupportedField index)
    let .list values := value | throw (.preflight .decodedType)
    if values.length != length then throw (.preflight .decodedType)
    let (entries, plan) ← (compileItems (fun pos => compileField cx output pos type) values).mapError (.nested index)
    return (.fixed type length entries, plan)
  | .list type, value => do
    if !Internal.supportedField type then throw (.unsupportedField index)
    let .list values := value | throw (.preflight .decodedType)
    let (entries, plan) ← (compileItems (fun pos => compileField cx output pos type) values).mapError (.nested index)
    return (.list type entries plan, plan)
  | .option type, value => do
    if !Internal.supportedField type then throw (.unsupportedField index)
    match value with
    | .variant 0 none => return (.sum (.option type) [none, some type] 0 none, [])
    | .variant 1 (some value) => do
      let (field, plan) ← (compileField cx output 0 type value).mapError (.nested index)
      return (.sum (.option type) [none, some type] 1 (some field), plan)
    | _ => throw (.preflight .decodedType)
  | .variant cases, value => do
    if !Internal.supportedCases cases then throw (.unsupportedField index)
    let .variant tag payload := value | throw (.preflight .decodedType)
    let (field, plan) ← (compileCases cx output cases tag payload).mapError (.nested index)
    return (.sum (.variant cases) (cases.map Prod.snd) tag field, plan)
  | .result ok error, value => do
    if !(Internal.supportedCase ok && Internal.supportedCase error) then throw (.unsupportedField index)
    let (tag, field, plan) ← match value with
      | .variant 0 payload => do
        let (field, plan) ← (compileCase cx output ok payload).mapError (.nested index)
        pure (0, field, plan)
      | .variant 1 payload => do
        let (field, plan) ← (compileCase cx output error payload).mapError (.nested index)
        pure (1, field, plan)
      | _ => throw (.preflight .decodedType)
    return (.sum (.result ok error) [ok, error] tag field, plan)
  | type, value => do
    let payload ← (checkValue type value).mapError (.preflight ∘ .schema)
    match type, payload with
    | .future element, ⟨.future id, _⟩ =>
      return (.endpoint .future element id, [.endpoint .future element id])
    | .stream element, ⟨.stream id, _⟩ =>
      return (.endpoint .stream element id, [.endpoint .stream element id])
    | .errorContext, ⟨.errorContext id, _⟩ => return (.context id, [.errorContext id])
    | type, payload =>
      match Stored.Lower.checkSchema type with
      | .ok () => return (.data type payload, [])
      | .error _ => throw (.unsupportedField index)

def compileFields {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) : List (String × TypeOf) → List Val → Except Issue (List Field × List Lower.Object)
  | [], [] => .ok ([], [])
  | (_, type) :: types, value :: values => do
    let (field, objects) ← compileField cx output index type value
    let (fields, rest) ← compileFields cx output (index + 1) types values
    return (field :: fields, objects ++ rest)
  | _, _ => .error (.preflight .decodedType)

def compileTypes {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output)
    (index : Nat) : List TypeOf → List Val → Except Issue (List Field × List Lower.Object)
  | [], [] => .ok ([], [])
  | type :: types, value :: values => do
    let (field, objects) ← compileField cx output index type value
    let (fields, rest) ← compileTypes cx output (index + 1) types values
    return (field :: fields, objects ++ rest)
  | _, _ => .error (.preflight .decodedType)

def compileCases {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output) :
    List (String × Option TypeOf) → Nat → Option Val → Except Issue (Option Field × List Lower.Object)
  | [], _, _ => .error (.preflight .decodedType)
  | (_, type) :: _, 0, payload => compileCase cx output type payload
  | _ :: rest, tag + 1, payload => compileCases cx output rest tag payload

def compileCase {E : CoreEngine} (cx : LiftLowerContext E) (output : Stored.Lower.Output) :
    Option TypeOf → Option Val → Except Issue (Option Field × List Lower.Object)
  | none, none => .ok (none, [])
  | some type, some payload => do
    let (field, plan) ← compileField cx output 0 type payload
    return (some field, plan)
  | _, _ => .error (.preflight .decodedType)
end

/-- Inspect every field before starting any field write or guest allocation. Plain fields
use the canonical data path; nested records and sum types participate in the same whole-record
plan. Every arm's schema is checked even when only one arm contributes effects. -/
def preflight {E : CoreEngine} (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) :
    Except Issue (List Field × List Lower.Object) := do
  let .record types := type | throw .notRecord
  (Stored.checkSchema type).mapError (.preflight ∘ .schema)
  (Stored.Lower.checkOptions cx type output).mapError (.preflight ∘ .abi)
  let .record values := payload.val | throw (.preflight .decodedType)
  compileFields cx output 0 types values

namespace Internal

def publishSlot {E : CoreEngine} {World : Type} (cx : LiftLowerContext E) (slot : Nat) :
    (output : Stored.Lower.Output) → P E World output.Result
  | .flat => pure [i32Flat slot]
  | .memory ptr => storeInt cx slot ptr 4

mutual
def runField {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (field : Field) (index : Nat)
    (output : Stored.Lower.Output) : P E (State sig) (Except Issue output.Result) :=
  match field with
  | .data type payload => do
    return (← Stored.Lower.lower limits quirks cx type payload output).mapError
      (.field index ∘ .beforeAllocation ∘ .abi)
  | .endpoint channel element id => do
    match ← ListLower.transfer limits cx channel element id with
    | .error issue => return .error (.field index (.beforeAllocation issue))
    | .ok slot => return .ok (← publishSlot cx slot output)
  | .context id => do
    if ((← getStore).errCtx? id).isNone then
      return .error (.field index (.beforeAllocation .missingContext))
    return .ok (← publishSlot cx (← lowerErrorContext limits cx id) output)
  | .aggregate type fields =>
    match output with
    | .flat => do return (← runFlat limits quirks cx width fields 0).mapError (.nested index)
    | .memory ptr => do
      checkInBounds cx ptr (layout width type).size
      return (← runMemory limits quirks cx width fields ptr 0).mapError (.nested index)
  | .fixed element _ entries =>
    match output with
    | .flat => do return (← runFlat limits quirks cx width entries 0).mapError (.nested index)
    | .memory ptr => do
      return (← runElements limits quirks cx width entries (layout width element).size ptr 0).mapError
        (.nested index)
  | .list element entries plan => do
    match Lower.prepare (← getStore) (← hostGet) plan with
    | .error issue => return .error (.field index (.beforeAllocation issue))
    | .ok _ =>
      let area := layout width element
      let ptr ← ListLower.allocateRange cx area entries.length
      match Lower.prepare (← getStore) (← hostGet) plan with
      | .error issue => return .error (.field index (.afterAllocation issue))
      | .ok _ =>
        match ← runElements limits quirks cx width entries area.size ptr 0 with
        | .error issue => return .error (.nested index issue)
        | .ok () => return .ok (← ListLower.publish cx width ptr entries.length output)
  | .sum type arms tag field =>
    match output with
    | .flat => do
      let joined := (flatten width type).drop 1
      match field with
      | none => return .ok (← lowerFlatVariantWith arms.length joined tag [] (pure []))
      | some field =>
        match ← runField limits quirks cx width field 0 .flat with
        | .error issue => return .error (.nested index issue)
        | .ok words =>
          return .ok (← lowerFlatVariantWith arms.length joined tag (flatten width field.type) (pure words))
    | .memory ptr => do
      let alignment := maxCaseAlignment (arms.map (layoutOption width))
      let address ← storeVariantHead cx arms.length alignment tag ptr
      match field with
      | none => return .ok ()
      | some field =>
        return (← runField limits quirks cx width field 0 (.memory address)).mapError (.nested index)

def runMemory {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) :
    List Field → Nat → Nat → P E (State sig) (Except Issue Unit)
  | [], _, _ => pure (.ok ())
  | field :: rest, cursor, index => do
    let area := layout width field.type
    let ptr := alignTo cursor area.alignment
    match ← runField limits quirks cx width field index (.memory ptr) with
    | .error issue => return .error issue
    | .ok () => runMemory limits quirks cx width rest (ptr + area.size) (index + 1)

def runElements {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) :
    List Field → Nat → Nat → Nat → P E (State sig) (Except Issue Unit)
  | [], _, _, _ => pure (.ok ())
  | field :: rest, stride, ptr, index => do
    match ← runField limits quirks cx width field index (.memory ptr) with
    | .error issue => return .error issue
    | .ok () => runElements limits quirks cx width rest stride (ptr + stride) (index + 1)

def runFlat {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) :
    List Field → Nat → P E (State sig) (Except Issue (List FlatValue))
  | [], _ => pure (.ok [])
  | field :: rest, index => do
    match ← runField limits quirks cx width field index .flat with
    | .error issue => return .error issue
    | .ok words =>
      let headWords : List FlatValue := words
      return (← runFlat limits quirks cx width rest (index + 1)).map (headWords ++ ·)
end

def emitRecord {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (type : TypeOf) (fields : List Field) :
    (output : Stored.Lower.Output) → P E (State sig) (Except Issue output.Result)
  | .flat => runFlat limits quirks cx width fields 0
  | .memory ptr => do
    let area := layout width type
    checkAligned ptr area.alignment.bytes
    checkInBounds cx ptr area.size
    runMemory limits quirks cx width fields ptr 0

end Internal

/-- Lower fields in canonical record order. A refusal of the whole record before the first
field is effect-free. An allocator can reenter: each effectful field checks the live store
again, and a list checks again after its own allocation. Field errors and traps do not
undo the completed prefix or the effects of realloc. -/
def lower {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type)
    (output : Stored.Lower.Output) : P E (State sig) (Except Issue output.Result) :=
  match preflight cx type payload output with
  | .error issue => pure (.error issue)
  | .ok (fields, plan) => do
    match Lower.prepare (← getStore) (← hostGet) plan with
    | .error issue => return .error (.preflight issue)
    | .ok _ =>
      let width ← ptrType cx
      if !Stored.Lower.fits quirks cx.opts.encoding width type payload.val then
        return .error (.preflight (.abi .allocationPrecondition))
      Internal.emitRecord limits quirks cx width type fields output

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
