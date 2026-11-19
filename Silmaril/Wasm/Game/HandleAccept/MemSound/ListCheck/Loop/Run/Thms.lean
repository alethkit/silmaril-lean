module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Soundness
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopTrace
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopCompact

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.MemSound (ReplyEnvs)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Items (itemsReply)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)

/-- Every finite correctly denoting reply plan produces an actual accepting export prefix,
including an empty vector or multiple occurrences of a child handle. This is a lower bound,
not termination under arbitrary hosts or equality with the memory32 length upper bound. -/
theorem accepts_of_plan {profile : Profile} (checker : Checker)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod checker.imports) mt instance_ initial)
    {Envs : Store Nat → SEnv UImp → Prop} {L : SEnv UImp} (env : Envs instance_.store L)
    (initState : L.S) {ready : Store Nat → Prop} (good : ready initial.store)
    {root : BitVec 32} {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (plan : ReplyPlan L ready checker.decodeChild root handles answerFor)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    (allowed : rho ∈ Rhos) {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom, answerFor handle = .atom atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile Envs 0 (Loop.mod checker.imports) checker.imports
      checker.decodeChild .trap policy Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_accepts
    checker spec env initState good plan policy allowed rootDenotes denotes atoms

theorem script_host_admitted {handles : List (BitVec 32)}
    {encodeChild : ByteArray → BitVec 32 → Except ReplyIssue ByteArray}
    (store : Store Nat) : ReplyEnvs itemsReply store (scriptHost handles encodeChild) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.script_admitted store

theorem compact_host_admitted {handles : List (BitVec 32)} {childBytes : BitVec 32 → ByteArray}
    (store : Store Nat) : ReplyEnvs itemsReply store (compactHost handles childBytes) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.compact_admitted store

/-- The checked encoder supplies the whole reply plan whenever the vector and child
payloads fit. The child decoder observes the bytes supplied for that exact handle. -/
theorem compact_reply_plan {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    {childBytes : BitVec 32 → ByteArray}
    (childFits : ∀ handle ∈ handles, (childBytes handle).size = capacity)
    (decode : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)) :
    ReplyPlan (compactHost handles childBytes) (ReplySpace capacity) decode root handles
      (fun handle => decode ⟨.values [], some (childBytes handle)⟩ 0) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.compact_plan width fits childFits decode

/-- In-place replies preserve the capacity, regardless of the bytes left by the previous
call. The child observation depends on the current payload, not on trailing memory. -/
theorem byte_reply_plan (checker : Checker) {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ capacity) :
    ReplyPlan (byteReplyHost handles raw) (ReplySpace capacity) checker.decodeChild root handles
      (fun handle => ((checker.decodeBytes (raw handle)).map SxA.atom).getD (.handle 0)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.bytes_plan checker width fits raw space

/-- Both checkers have a validated instance with one initial memory page. -/
theorem checker_instance (checker : Checker) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports) mt instance_ initial ∧
      ReplySpace 65536 initial.store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_instance checker

/-- The compact script realizes the accepted tree in an actual module instance, using
only shaped host replies. The required capacity includes the eight-byte list header. -/
theorem compact_accepts {profile : Profile} (checker : Checker)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod checker.imports) mt instance_ initial)
    {capacity : Nat} (width : capacity ≤ 2 ^ 32) (good : ReplySpace capacity initial.store)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    {childBytes : BitVec 32 → ByteArray} (childFits : ∀ handle ∈ handles, (childBytes handle).size = capacity)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    (allowed : rho ∈ Rhos) {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeChild ⟨.values [], some (childBytes handle)⟩ 0 = .atom atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports) checker.imports
      checker.decodeChild .trap policy Rhos :=
  accepts_of_plan checker spec (compact_host_admitted instance_.store) () good
    (compact_reply_plan width fits childFits checker.decodeChild) policy allowed rootDenotes denotes atoms

/-- The validated one-page checker accepts any correctly denoting byte script fitting the
page. The checked encoders construct both kinds of reply in place. -/
theorem byte_reply_accepts {profile : Profile} (checker : Checker)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ 65536)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ 65536)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports)
      checker.imports checker.decodeChild .trap policy Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.bytes_accepts
    checker policy allowed fits raw space rootDenotes denotes atoms

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
