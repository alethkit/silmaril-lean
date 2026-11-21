module

import Batteries.Data.Except
import Silmaril.Formats.Git.Filesystem.Thms
meta import Silmaril.Formats.Cbor.Drisl.Cid.Defs
meta import Silmaril.Formats.Git.Arena.Defs
meta import Silmaril.Formats.Git.Filesystem.Defs
meta import Silmaril.Semantics.Arena.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Arena (CasLane Read)
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Prolly (ByteKey)

private abbrev Item := Σ mode : EntryMode, Object ByteKey String Unit mode.kind
private abbrev Snapshot := Object ByteKey String Unit .tree

private def emptyDir : Directory ByteKey Item := ⟨∅, fun key => False.elim (Finset.notMem_empty _ key.property)⟩

private def toTree (dir : Directory ByteKey Item) : Snapshot :=
  .tree dir.keys (fun key => (dir.get key).1) (fun key => (dir.get key).2)

private def nativeRaw : ByteKey := [255]
private def dirKey : ByteKey := Dasl.utf8Key "dir"
private def symlinkKey : ByteKey := Dasl.utf8Key "link"
private def body : ByteArray := "echo ok\n".toByteArray
private def symlinkBody : ByteArray := "dir/".toByteArray.push 255

private def fixture : Snapshot :=
  let nested := toTree (emptyDir.insert nativeRaw ⟨.file .executable, .blob body⟩)
  toTree ((emptyDir.insert dirKey ⟨.directory, nested⟩).insert symlinkKey ⟨.file .symlink, .blob symlinkBody⟩)

private def mock (wire : ByteArray) : Digest :=
  let stamp := wire.toList.foldl (fun total byte => total * 65599 + byte.toUInt64) (0 : UInt64)
  ⟨(List.ofFn fun index : Fin 8 => (stamp >>> (8 * index.val.toUInt64)).toUInt8) ++ List.replicate 24 0, by simp⟩

private def require (message : String) (claim : Prop) [Decidable claim] : Except String Unit :=
  if claim then .ok () else .error message

private def arenaProfile (hash : Hash) : Arena.Profile Cid ByteArray where
  kind := fun _ => none
  gitBytes := fun _ _ => none
  gitHash := fun _ _ => none
  casBytes := fun _ bytes => some bytes
  casName lane bytes := some (address hash lane bytes)

private def arenaStore (hash : Hash) (writes : Writes) : Except String Store := do
  let profile := arenaProfile hash
  let empty : Arena.State writes.length Cid ByteArray := Silmaril.Semantics.Arena.State.empty
  let resident ← (List.finRange writes.length).foldlM (init := empty) fun state index => do
    let (cid, bytes) := writes[index.val]
    let lane : CasLane := if laneMatches .raw cid then .raw else .object
    let occupied ← (state.step profile index (.insert bytes)).mapError fun fault => reprStr fault
    let (id, named) ← (occupied.assign profile index (.cas lane)).mapError fun fault => reprStr fault
    require "arena assigned the canonical address" (id = .cas lane cid)
    pure named
  pure (Store.ofArena profile resident)

private def checkMount (hash : Hash) (mount : Store) (root : Cid) : Except String Unit := do
  let .ok (some binary) := locate hash mount 8 root [dirKey, nativeRaw] | .error "missing executable at raw path"
  require "raw name has no UTF-8 façade spelling" (Dasl.decodeComponent nativeRaw = none)
  require "executable and bytes roundtrip" (binary.mode = .file .executable ∧ openBlob hash mount binary = .found body)
  let .some link := Component.parse? "link" | .error "invalid fixture name"
  let .ok (some symlink) := locateUtf8 hash mount 8 root [link] | .error "missing symlink at String path"
  require "symlink mode and target bytes preserved" (symlink.mode = .file .symlink ∧
    openBlob hash mount symlink = .found symlinkBody)
  require "no implicit symlink following" (locate hash mount 8 root [symlinkKey, nativeRaw] = .error .notDirectory)
  require "closed-view absence" (locate hash mount 8 root [dirKey, Dasl.utf8Key "absent"] = .ok none)

private def exercise (hash : Hash) : Except String Cid := do
  let staged ← (stage hash fixture).mapError fun fault => reprStr fault
  let .ok published := staged.publish (fun _ => none) | .error "fixture has an address conflict"
  require "raw and object lanes use different envelopes" (address hash .raw body ≠ address hash .object body)
  checkMount hash (Store.ofPublished published) staged.name
  checkMount hash (← arenaStore hash staged.writes) staged.name
  let blocked : Store := fun lane cid =>
    if cid = staged.name then .deferred else (Store.ofPublished published) lane cid
  require "deferred block is not an absent path"
    (locate hash blocked 8 staged.name [dirKey] = .error (.deferred staged.name))
  let gitlink := toTree (emptyDir.insert dirKey ⟨.gitlink, .ref .commit "external-commit"⟩)
  let .error (.gitlink key) := stage hash gitlink | .error "gitlink imported as a local subtree"
  require "gitlink retains its boundary key" (key = dirKey)
  let wrongName := toTree (emptyDir.insert [0] ⟨.file .regular, .blob body⟩)
  let .error (.component key) := stage hash wrongName | .error "invalid NUL component accepted"
  require "component rejection reports its byte key" (key = [0])
  match staged.publish (fun cid => if cid = staged.name then some ByteArray.empty else none) with
  | .ok _ => .error "publication overwrote conflicting bytes"
  | .error cid =>
    require "conflicting root stays unchanged" (cid = staged.name)
    pure staged.name

private def parseNibble (char : Char) : Option Nat :=
  if '0' ≤ char ∧ char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char ∧ char ≤ 'f' then some (10 + char.toNat - 'a'.toNat)
  else none

private def parseHex : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
    let high ← parseNibble high
    let low ← parseNibble low
    return (UInt8.ofNat (16 * high + low)) :: (← parseHex rest)
  | [_] => none

private def externalDigest (command : String) (wire : ByteArray) : IO Digest :=
  IO.FS.withTempFile fun _ path => do
    IO.FS.writeBinFile path wire
    let output ← IO.Process.output { cmd := command, args := #[path.toString] }
    let some text := (output.stdout.splitOn " ").head? | throw (IO.userError "missing b3sum digest")
    let some bytes := parseHex text.toList | throw (IO.userError "invalid hex from b3sum")
    if width : bytes.length = 32 then
      if output.exitCode = 0 then pure ⟨bytes, width⟩ else throw (IO.userError "b3sum failed")
    else throw (IO.userError "b3sum produced a non-32-byte digest")

private abbrev DigestTable := List (ByteArray × Digest)

private def tableHash (seen : DigestTable) : Hash := fun wire =>
  ((seen.find? fun entry => decide (entry.1 = wire)).map Prod.snd).getD ⟨List.replicate 32 0, by simp⟩

/-- Only fixture preimages are supplied by the external hash executable. Iterate
until every block in the final replay has a checked fixture digest. -/
private def calculateFixture (command : String) : Nat → DigestTable → IO DigestTable
  | 0, _ => throw (IO.userError "external digest table did not stabilize")
  | fuel + 1, seen => do
    let hash := tableHash seen
    let .ok image := stage hash fixture | throw (IO.userError "fixture staging failed")
    let missing := image.writes.filterMap fun (_, wire) =>
      if seen.any (fun entry => decide (entry.1 = wire)) then none else some wire
    if missing.isEmpty then pure seen else
      let more ← missing.mapM fun wire => do pure (wire, ← externalDigest command wire)
      calculateFixture command fuel (seen ++ more)

public def main (args : List String) : IO Unit := do
  let hash ← match args with
    | [] => pure mock
    | [command] => tableHash <$> calculateFixture command 8 []
    | _ => throw (IO.userError "usage: GitFilesystem.lean [b3sum executable]")
  match exercise hash with
  | .ok cid =>
    let text := (Silmaril.Formats.Cbor.Drisl.Cid.codec .bdasl).render cid
    IO.println s!"Git tree → BDASL → CID-only reads passed; tree CID {text}"
  | .error detail => throw (IO.userError detail)

#print axioms names_iff
#print axioms Image.publish_bindings
#print axioms Image.readPublished
#print axioms readVerified_found
#print axioms lookupChild_sound
