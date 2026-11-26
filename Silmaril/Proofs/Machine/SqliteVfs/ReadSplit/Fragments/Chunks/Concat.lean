module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Chunks

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit (combine)
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments (readFragments)

private theorem combine_assoc (left middle right : ReadReply) :
    (combine middle right).bind (combine left) =
      (combine left middle).bind (fun combined => combine combined right) := by
  cases left <;> cases middle <;> cases right <;> simp [combine, List.append_assoc]

private theorem combine_bind_assoc (left : ReadReply) (middle right : Option ReadReply) :
    (middle.bind (fun reply => right.bind (combine reply))).bind (combine left) =
      (middle.bind (combine left)).bind (fun reply => right.bind (combine reply)) := by
  cases middle with
  | none => rfl
  | some middle =>
    cases right with
    | none =>
      change none = (combine left middle).bind (fun _ => none)
      cases combine left middle <;> rfl
    | some right => exact combine_assoc left middle right

private theorem combine_empty_prefix (left : ReadReply) (right : Option ReadReply) :
    right.bind (combine left) =
      (combine (.ok []) left).bind (fun reply => right.bind (combine reply)) := by
  cases left <;> cases right <;> rfl

/-- Two nonempty ordered chunks use the same exchanges, actual endpoint and
aggregate reply as their concatenated fragment schedule. -/
theorem read_fragments_chunks {State : Type} (handler : Handler State)
    (handle : Handle) (start : State) (offset firstCount : Nat) (firstRest : List Nat)
    (secondCount : Nat) (secondRest : List Nat) :
    let first := readFragments handler handle start offset firstCount firstRest
    let second := readFragments handler handle first.file (offset + firstCount + firstRest.sum)
      secondCount secondRest
    let together := readFragments handler handle start offset firstCount
      (firstRest ++ (secondCount :: secondRest))
    together.file = second.file ∧ together.trace = first.trace ++ second.trace ∧
      together.reply = first.reply.bind (fun reply => second.reply.bind (combine reply)) := by
  induction firstRest generalizing start offset firstCount with
  | nil =>
    let request := Request.read handle offset firstCount
    let call := handler start request
    let second := readFragments handler handle call.2 (offset + firstCount) secondCount secondRest
    change second.file = second.file ∧
      ⟨request, call.1⟩ :: second.trace = [⟨request, call.1⟩] ++ second.trace ∧
      second.reply.bind (combine call.1) =
        (combine (.ok []) call.1).bind (fun reply => second.reply.bind (combine reply))
    exact ⟨rfl, rfl, combine_empty_prefix _ _⟩
  | cons next rest ih =>
    let request := Request.read handle offset firstCount
    let call := handler start request
    let first := readFragments handler handle call.2 (offset + firstCount) next rest
    let second := readFragments handler handle first.file
      (offset + firstCount + next + rest.sum) secondCount secondRest
    let both := readFragments handler handle call.2 (offset + firstCount) next
      (rest ++ (secondCount :: secondRest))
    obtain ⟨file, trace, reply⟩ := ih call.2 (offset + firstCount) next
    have offset_eq : offset + firstCount + (next + rest.sum) =
        offset + firstCount + next + rest.sum := (Nat.add_assoc ..).symm
    simp only [List.sum_cons, offset_eq]
    change both.file = second.file ∧
      ⟨request, call.1⟩ :: both.trace =
        (⟨request, call.1⟩ :: first.trace) ++ second.trace ∧
      both.reply.bind (combine call.1) =
        (first.reply.bind (combine call.1)).bind (fun reply => second.reply.bind (combine reply))
    refine ⟨file, congrArg (List.cons ⟨request, call.1⟩) trace, ?_⟩
    change both.reply = first.reply.bind (fun reply => second.reply.bind (combine reply)) at reply
    rw [reply]
    exact combine_bind_assoc _ _ _

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments.Chunks
