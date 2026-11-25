module

public import Silmaril.Courses.Cambridge.L2.OperationalInstitution
public import Silmaril.Courses.Cambridge.L2.Typing
public import Silmaril.Wasm.Game.ULink.Thms

/-! # An L2 callback at the Wasm 3 shared-store boundary

The L2 term applies a higher-order function to a callback. A designated
store cell supplies the answer read inside the callback. The Wasm side
uses the existing linked provider and consumer and projects their actual
game moves to a finite ground observation.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.WasmCallback

open Silmaril.Games
open Silmaril.Wasm.Execution.Core (Result Val)
open Silmaril.Wasm.Game (UImp UReply)
open Silmaril.Wasm.Game.ULinkCallback (cbLink cbS hostQ runPlay runQ)
open Silmaril.Wasm.Numerics (Profile)

def replyCell : Loc := "reply"

def apply : Expr := .lam (.arr .unit .int) (.app (.bvar 0) .skip)
def callback : Expr := .lam .unit (.deref replyCell)
def program : Expr := .app apply callback

def context : TypeEnv :=
  { TypeEnv.empty with locs := (∅ : L1.TypeEnv).insert replyCell .intref }

theorem program_typed : HasType context program .int :=
  .app (.lam (.app (.bvar rfl) .skip)) (.lam (.deref (by simp [context, TypeEnv.push])))

/-- The two beta steps reach the read inside the callback in the original store. -/
theorem reaches_read (s : Store) :
    lts.MTr ⟨program, s⟩ [(), ()] ⟨.deref replyCell, s⟩ :=
  .stepL (Step.appFun (.lam .unit (.deref replyCell))) (.stepL (Step.appFun .skip) .refl)

theorem returns (s : Store) (word : BitVec 32)
    (reply : L1.Store.lookup s replyCell = some word.toInt) :
    OperationalInstitution.semantics.May ⟨program, s⟩ (.returned ⟨.int word.toInt, s⟩) := by
  have toRead := steps_iff_reachable.2 ⟨[(), ()], reaches_read s⟩
  exact (OperationalInstitution.may_return_iff _ _).2
    ⟨toRead.tail (.deref reply), .int word.toInt⟩

/-- Public moves of this pilot, with stores projected away. Host requests
retain their target and arguments. Answers expose signed scalar payloads. -/
inductive Event where
  | entry (args : List Val)
  | request (host : Nat) (args : List Val)
  | reply (host : Nat) (value : Int)
  | returned (value : Int)

def signedResult : Result → Option Int
  | .values [.num ⟨.int .i32, word⟩] => some word.toInt
  | _ => none

abbrev GameMove := Move UImp cbLink.U.F

def observe : GameMove → Option Event
  | .inr (.ask q) => some (.entry q.args)
  | .inl (.ask q) => some (.request q.target q.args)
  | .inl (.ans q a) => (signedResult a.result).map (.reply q.target)
  | .inr (.ans _ a) => (signedResult a.result).map .returned

theorem observe_stub (play : List GameMove) :
    (play.map cbLink.stubUp).mapM observe = play.mapM observe := by
  rw [List.mapM_map]
  apply congrArg (fun read => List.mapM read play)
  funext move
  rcases move with move | move <;> cases move <;> rfl

/-- The two actual game moves that expose the pending host request. -/
def requestPlay : List GameMove := [.inr (.ask runQ), .inl (.ask hostQ)]

/-- Reaching the L2 read agrees with the pending request at the Wasm boundary.
This observation is available before a reply is supplied. -/
theorem request_agrees (P : Profile) (s : Store) :
    lts.MTr ⟨program, s⟩ [(), ()] ⟨.deref replyCell, s⟩ ∧
      requestPlay ∈ cbLink.U.strategy P ∧
      requestPlay.map cbLink.stubUp ∈ cbLink.compStrategy P ∧
      requestPlay.mapM observe = some [.entry [], .request 0 []] ∧
      (requestPlay.map cbLink.stubUp).mapM observe = requestPlay.mapM observe := by
  let answer : UReply := ⟨cbS, .values [Val.i32 0]⟩
  have initialSegment : requestPlay <+: runPlay answer :=
    ⟨[.inl (.ans hostQ answer), .inr (.ans runQ answer)], rfl⟩
  exact ⟨reaches_read s,
    (cbLink.U.strategy P).of_prefix
      (Silmaril.Wasm.Game.ULinkCallback.linked_play P cbS (Val.i32 0)) initialSegment,
    (cbLink.compStrategy P).of_prefix
      (Silmaril.Wasm.Game.ULinkCallback.comp_play_cbS P (Val.i32 0))
      (initialSegment.map cbLink.stubUp),
    rfl, observe_stub requestPlay⟩

/-- The L2 read of the supplied signed word agrees with a completed Wasm play
through the linked instance and its provider/consumer composite. This is
existence of a matching finite play for each supplied reply. -/
theorem agrees (P : Profile) (s : Store) (word : BitVec 32)
    (reply : L1.Store.lookup s replyCell = some word.toInt) :
    OperationalInstitution.semantics.May ⟨program, s⟩ (.returned ⟨.int word.toInt, s⟩) ∧
      ∃ play : List GameMove,
        play ∈ cbLink.U.strategy P ∧
        play.map cbLink.stubUp ∈ cbLink.compStrategy P ∧
        play.mapM observe = some [.entry [], .request 0 [], .reply 0 word.toInt, .returned word.toInt] ∧
        (play.map cbLink.stubUp).mapM observe = play.mapM observe := by
  refine ⟨returns s word reply, runPlay ⟨cbS, .values [Val.i32 word]⟩, ?_, ?_, ?_, ?_⟩
  · exact Silmaril.Wasm.Game.ULinkCallback.linked_play P cbS (Val.i32 word)
  · exact Silmaril.Wasm.Game.ULinkCallback.comp_play_cbS P (Val.i32 word)
  · rfl
  · exact observe_stub _

-- The all-ones Wasm word is observed as the L2 integer `-1`.
example (P : Profile) :
    ∃ play : List GameMove, play ∈ cbLink.U.strategy P ∧
      play.mapM observe = some [.entry [], .request 0 [], .reply 0 (-1), .returned (-1)] := by
  let s := L1.Store.empty.insert replyCell (-1)
  have reply : L1.Store.lookup s replyCell = some ((0xffffffff : BitVec 32).toInt) := by decide
  obtain ⟨_, play, linked, _, trace, _⟩ := agrees P s 0xffffffff reply
  exact ⟨play, linked, trace⟩

end Silmaril.Courses.Cambridge.L2.WasmCallback
