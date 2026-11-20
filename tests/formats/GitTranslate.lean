module

import Silmaril.Crypto.SHA1.Thms
import Silmaril.Crypto.SHA256
import Silmaril.Formats.Dasl.Wire.Defs
import Silmaril.Formats.Git.Dasl.Layouts.Thms
import Silmaril.Formats.Git.Translate.Thms
meta import Silmaril.Crypto.SHA1.Thms
meta import Silmaril.Crypto.SHA256
meta import Silmaril.Formats.Dasl.Wire.Defs
meta import Silmaril.Formats.Git.Dasl.Layouts.Thms
meta import Silmaril.Formats.Git.Translate.Thms

open Silmaril Silmaril.Formats.Git Silmaril.Formats.Git.Translate
open Silmaril.Formats.Dasl (Shallow)
open Silmaril.Formats.Dasl.Wire (Cid)

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def repeated (algorithm : Native.Algorithm) (byte : UInt8) : Native.NameBytes algorithm :=
  ⟨⟨Array.replicate algorithm.width byte⟩, by simp [ByteArray.size]⟩

private def nativeHash : (algorithm : Native.Algorithm) → ByteArray → Native.NameBytes algorithm
  | .sha1, wire => ⟨(Crypto.sha1 wire.toList).toByteArray, by simp [Native.Algorithm.width, Crypto.SHA1.digest_length]⟩
  | .sha256, wire => ⟨(Crypto.SHA256.digest wire.toList).toByteArray,
      by simp [Native.Algorithm.width, Crypto.SHA256.digest_length]⟩

private def objectZero : Cid := ⟨[1, 0x71, 0x12, 32] ++ List.replicate 32 0, by decide⟩
private def rawZero : Cid := ⟨[1, 0x55, 0x12, 32] ++ List.replicate 32 0, by decide⟩

private def cidHash (tag : UInt8) (wire : ByteArray) : Option Cid :=
  (Formats.Cbor.Drisl.Cid.codec .dasl).parse? ([1, tag, 0x12, 32] ++ Crypto.SHA256.digest wire.toList)

private def objectBytes? := Formats.Dasl.Wire.render?

private def namer : Dasl.Naming Cid :=
  ⟨fun value => ((objectBytes? value).bind (cidHash 0x71)).getD objectZero,
    fun wire => (cidHash 0x55 wire).getD rawZero⟩

private def model (algorithm : Native.Algorithm) (layout : Dasl.Layout String Cid) :
    Profile algorithm String (Native.NameBytes algorithm) Cid Metadata where
  native := ⟨Dasl.utf8KeyCodec, Native.nameBytesCodec algorithm, nativeHash algorithm⟩
  naming := namer
  layout := layout
  valid := validComponent
  metadata := fun data => ⟨data.message.toByteArray, Int64.ofNat data.committer.seconds⟩
  codec := Dasl.metadataCodec
  frontier := fun kind name =>
    if decide (kind = .commit) && name.val == (repeated algorithm 0x77).val then
      cidHash 0x71 "external".toByteArray
    else none

private def tree (algorithm : Native.Algorithm) : Object String (Native.NameBytes algorithm) Native.CommitMetadata .tree :=
  .tree {"a", "b", "sub"}
    (fun key => if key.val = "sub" then .gitlink else .file (if key.val = "a" then .regular else .symlink))
    (fun key => by
      split
      · exact .ref .commit (repeated algorithm 0x77)
      · exact .blob "payload\n".toByteArray)

private def metadata (message : String) : Native.CommitMetadata :=
  ⟨⟨"Author", "a@example.test", 10⟩, ⟨"Committer", "c@example.test", 20⟩, message⟩

private def hex (bytes : ByteArray) : String :=
  let digit := fun value : Nat => Char.ofNat (if value < 10 then 48 + value else 87 + value)
  String.ofList (bytes.toList.flatMap fun byte => [digit (byte.toNat / 16), digit (byte.toNat % 16)])

private def exercise (algorithm : Native.Algorithm) (expected : String) : IO Cid := do
  let profile := model algorithm .dict
  let root := tree algorithm
  let ancestor (message : String) := Object.commit root 0 Fin.elim0 (metadata message)
  let merge := Object.commit root 3 (fun index => ancestor (if index.val = 1 then "one\n" else "two\n"))
    (metadata "merge\n")
  let some gitlink := translate profile (.ref .commit (repeated algorithm 0x77)) |
    throw (IO.userError "mapped gitlink should remain an opaque link")
  check ((translate profile (.ref .tree (repeated algorithm 0x77))).isNone) "frontier map is kind-specific"
  check ((translate { profile with frontier := fun _ _ => none } merge).isNone) "unmapped gitlink rejects fold"
  let some translated := translate profile merge | throw (IO.userError "translate dictionary commit")
  let some targetTree := translate profile root | throw (IO.userError "translate dictionary tree")
  let some first := translate profile (ancestor "one\n") | throw (IO.userError "translate first parent")
  let some second := translate profile (ancestor "two\n") | throw (IO.userError "translate second parent")
  let targetEntries : ShallowTree String Cid := ⟨{"a", "b", "sub"}, fun key =>
    if key.val = "sub" then ⟨.gitlink, gitlink.target.root⟩ else
      ⟨.file (if key.val = "a" then .regular else .symlink), namer.blob "payload\n".toByteArray⟩⟩
  let some treeBytes := objectBytes? (Dasl.dictDirectory.encode targetEntries) |
    throw (IO.userError "canonical dictionary tree bytes")
  check ((cidHash 0x71 treeBytes).map Subtype.val == some targetTree.target.root.val)
    "gitlink remains an object link and regular file and symlink share a raw link"
  let targetCommit := (Dasl.namedCommit Dasl.metadataCodec).encode
    ⟨targetTree.target.root, [second.target.root, first.target.root, second.target.root], ⟨"merge\n".toByteArray, 20⟩⟩
  let some targetBytes := objectBytes? targetCommit | throw (IO.userError "canonical commit bytes")
  check ((cidHash 0x71 targetBytes).map Subtype.val == some translated.target.root.val)
    "bottom-up commit hashes the canonical bytes with ordered, repeated parents"
  let some parsed := (Formats.Dasl.Wire.parse? targetBytes).bind (Dasl.namedCommit Dasl.metadataCodec).decode? |
    throw (IO.userError "canonical commit roundtrip")
  check (parsed.parents.map Subtype.val == [second.target.root.val, first.target.root.val, second.target.root.val])
    "canonical bytes retain ordered, repeated parent links"
  check (hex translated.source.val == expected) "translated native name matches independent Git fixture"
  let policy : Semantics.Prolly.Policy String := ⟨2, by decide, fun _ _ => false⟩
  for layout in [Dasl.Layout.stringList, Dasl.Layout.stringProlly policy] do
    let some alternate := translate (model algorithm layout) merge | throw (IO.userError "alternate layout")
    check (alternate.source.val == translated.source.val) "layout does not affect the native name"
    check (alternate.target.root.val != objectZero.val) "alternate layout has a serializable commit"
    check (alternate.target.root.val != translated.target.root.val) "layout affects the canonical target name"
  pure translated.target.root

public def main : IO Unit := do
  let fromSHA1 ← exercise .sha1 "3c550f58242cd06b475ce597a018d2fa6889f9e6"
  let fromSHA256 ← exercise .sha256 "71d3381193ea759c83f1f2d39e6dbcdf832dbd9a0c69b7d1eeaed4f59b3cd14b"
  check (fromSHA1.val == fromSHA256.val) "for the same target graph, changing native hash does not change the target name"
  IO.println "Git translation checks passed"

#print axioms translate
#print axioms translate_root_pair
#print axioms translate_native
#print axioms translate_commit_evidence
#print axioms Audit.sameTarget
