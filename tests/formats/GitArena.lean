module

import Silmaril.Formats.Git.Arena.Thms
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Native.Defs
meta import Silmaril.Semantics.Arena.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena

private inductive Content where
  | blob (bytes : ByteArray)
  | tree (description : ByteArray)
  | anonymous
  deriving DecidableEq

private def digest (algorithm : Native.Algorithm) : Native.NameBytes algorithm :=
  ⟨⟨Array.replicate algorithm.width 7⟩, by simp [ByteArray.size]⟩

private def profile : Profile String Content where
  kind
    | .blob _ => some .blob
    | .tree _ => some .tree
    | .anonymous => none
  gitBytes _
    | .blob bytes => some (Native.loose .blob bytes)
    | _ => none
  gitHash algorithm _ := some (digest algorithm)
  casBytes
    | .raw, .blob bytes => some bytes
    | .object, .tree bytes => some bytes
    | _, _ => none
  casName _ _ := some "demo"

private def checked {Value : Type} (result : Except Fault Value) : Except String Value :=
  result.mapError (fun fault => s!"unexpected fault: {repr fault}")

private def require (message : String) (claim : Prop) [Decidable claim] : Except String Unit :=
  if claim then .ok () else .error message

private def fails {Value : Type} (result : Except Fault Value) (want : Fault) : Bool :=
  match result with | .ok _ => false | .error fault => decide (fault = want)

private def exercise : Except String Unit := do
  let empty : State 6 String Content := Silmaril.Semantics.Arena.State.empty
  let first : ByteArray := ⟨#[1, 2]⟩
  let second : ByteArray := ⟨#[3, 4]⟩
  let oid := Oid.sha1 (digest .sha1)
  let git : Arena.Id String := .git oid
  let raw : Arena.Id String := .cas .raw "demo"
  let a ← checked (empty.step profile 0 (.reserve git (some .blob)))
  let b ← checked (a.step profile 1 (.reserve git))
  let c ← checked (b.step profile 2 (.reserve raw))
  require "typed Git placeholder" (c.readGit profile oid (some .blob) = .placeholder)
  require "known incompatible kind" (c.readGit profile oid (some .tree) = .invalid)
  require "CAS placeholder independent of Git" (c.readCas profile .raw "demo" = .placeholder)
  require "unknown object lane" (c.readCas profile .object "demo" = .unindexed)
  require "fetch absence is not defer" (fails (c.cache profile 0 git (fun _ => .missing)) .missing = true)
  require "shallow fetch boundary" (fails (c.cache profile 0 git (fun _ => .deferred)) .deferred = true)
  require "wrong returned kind rejected" (fails (c.cache profile 0 git (fun _ => .found (.tree first))) .invalid = true)
  require "placeholder cannot be hashed" (fails (c.assign profile 1 (.git .sha256)) .unavailable = true)
  let (_, d) ← checked (c.cache profile 0 git (fun _ => .found (.blob first)))
  require "lookup through aliases" (d.readGit profile oid = .found (Native.loose .blob first))
  require "a matching digest is not evidence of equality"
    (fails (d.cache profile 1 git (fun _ => .found (.blob second))) .conflict = true)
  let (_, aliasFilled) ← checked (d.cache profile 1 git (fun _ => .found (.blob first)))
  let (_, hit) ← checked (aliasFilled.cache profile 0 git (fun _ => .invalid))
  let (sha256, e) ← checked (hit.assign profile 0 (.git .sha256))
  require "second algorithm's tagged name" (sha256 = .git (.sha256 (digest .sha256)))
  require "old algorithm stays readable" (e.readGit profile oid = .found (Native.loose .blob first))
  let (_, f) ← checked (e.cache profile 2 raw (fun _ => .found (.blob first)))
  let (_, g) ← checked (f.assign profile 0 (.cas .raw))
  let h ← checked (g.step profile 3 (.insert (.tree second)))
  require "Git-less tree" (fails (h.assign profile 3 (.git .sha1)) .unavailable = true)
  let (_, i) ← checked (h.assign profile 3 (.cas .object))
  require "typed CAS lanes retain different bytes" (i.readCas profile .raw "demo" = .found first ∧
    i.readCas profile .object "demo" = .found second)
  let j ← checked (i.step profile 4 (.insert .anonymous))
  require "neither name required" (fails (j.assign profile 4 (.cas .object)) .unavailable = true)
  let inconsistent : State 6 String Content := Silmaril.Semantics.Arena.State.replaceAt j 1
    (some ⟨some ⟨[git], some .blob⟩, some (.blob second)⟩)
  require "unchecked snapshots do not pick a winner" (inconsistent.readGit profile oid = .conflict)

public def main : IO Unit :=
  match exercise with
  | .ok () => IO.println "Git arena checks passed"
  | .error detail => throw (IO.userError detail)

#print axioms State.empty_valid
#print axioms State.codecView_keyName
#print axioms Profile.different_derived
#print axioms State.step_spec
#print axioms State.valid_step
#print axioms State.step_extends
#print axioms State.extends_observed
#print axioms State.reserve_spec
#print axioms State.insert_spec
#print axioms State.materialize_spec
#print axioms State.assign_spec
#print axioms State.insert_attach_commutes
#print axioms State.cache_spec
#print axioms State.cache_valid_observed
#print axioms State.observed_binding
#print axioms State.observed_provenance
#print axioms State.observed_refines
#print axioms State.mem_candidates
#print axioms State.lookup_found_iff
#print axioms State.readWire_found
