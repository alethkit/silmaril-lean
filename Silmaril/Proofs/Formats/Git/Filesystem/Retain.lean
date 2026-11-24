module

public import Silmaril.Formats.Git.Filesystem.Retain.Defs
public import Silmaril.Formats.Git.Filesystem.Routed.Thms
public import Silmaril.Formats.Git.Filesystem.Writer.Thms
public import Silmaril.Formats.Dasl.Wire.Canonical.Thms

public section

namespace Silmaril.Proofs.Formats.Git.Filesystem

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Prolly (ByteKey Stored)
open Silmaril.Formats.Dasl.Wire (Profile bdasl_roundtrip)
open Silmaril.Formats.Git.Arena (CasLane Read)
open Silmaril.Semantics
open Silmaril.Semantics.Prolly (build replayAddress)

variable {hash : Hash} {Ref Meta : Type} {kind : Kind}

theorem directoryCid_eq_stageDirectory (hash : Hash) (directory : ByteDirectory) :
    directoryCid hash directory = (stageDirectory hash directory).map Image.name := by
  unfold directoryCid
  cases named : (build policy directory.ordered).rootName? (dirProfile hash).nameBlock? with
  | none => simp [stageDirectory, named, Except.map]
  | some root =>
    obtain ⟨image, success, certified⟩ := stageDirectory_of_root named
    have replay := ((build policy directory.ordered).replayAddress_spec (dirProfile hash).nameBlock? image.name named).2
    have same : image.name = root := certified.1.symm.trans replay
    simp [success, Except.map, same]

private theorem scan_map {Index Error : Type} [DecidableEq Index] {Value Out : Index → Type}
    (convert : (index : Index) → Value index → Out index) :
    ∀ (items : List Index) (visit : (index : Index) → index ∈ items → Except Error (Value index)),
      Translate.Graph.scan items (fun index hit => (visit index hit).map (convert index)) =
        (Translate.Graph.scan items visit).map (fun read index hit => convert index (read index hit)) := by
  intro items
  induction items with
  | nil =>
    intro visit
    exact congrArg Except.ok (funext fun _ => funext fun hit => (List.not_mem_nil hit).elim)
  | cons first rest ih =>
    intro visit
    let tailVisit := fun index hit => visit index (List.mem_cons_of_mem first hit)
    have left : Translate.Graph.scan (first :: rest) (fun index hit => (visit index hit).map (convert index)) = (do
        let value ← (visit first List.mem_cons_self).map (convert first)
        let tail ← Translate.Graph.scan rest (fun index hit => (tailVisit index hit).map (convert index))
        pure (fun index hit => if same : index = first then same.symm ▸ value
          else tail index ((List.mem_cons.mp hit).resolve_left same))) := rfl
    have right : Translate.Graph.scan (first :: rest) visit = (do
        let value ← visit first List.mem_cons_self
        let tail ← Translate.Graph.scan rest tailVisit
        pure (fun index hit => if same : index = first then same.symm ▸ value
          else tail index ((List.mem_cons.mp hit).resolve_left same))) := rfl
    rw [left, right, ih tailVisit]
    cases visit first List.mem_cons_self with
    | error fault => rfl
    | ok value =>
      cases Translate.Graph.scan rest tailVisit with
      | error fault => rfl
      | ok tail =>
        apply congrArg Except.ok
        funext index hit
        by_cases same : index = first
        · subst index; simp
        · simp [same]

private def treeImage {keys : Finset ByteKey} {modes : ↥keys → EntryMode}
    (root : Image hash .tree) (images : (child : ↥keys) → Image hash (modes child).kind) : Image hash .tree :=
  let order := keys.attach.sort (· ≤ ·)
  let descendants := order.attach.flatMap fun child => (images child.val).writes
  { root with descendants := root.descendants ++ descendants }

theorem rootCid_eq_stage (hash : Hash) (tree : Object ByteKey Ref Meta kind) :
    rootCid hash tree = (stage hash tree).map Image.name := by
  induction tree with
  | blob bytes => rfl
  | ref kind name => rfl
  | commit tree count parents metadata ihTree ihParent => rfl
  | tree keys modes children ih =>
    let order := keys.attach.sort (· ≤ ·)
    have member (child : ↥keys) : child ∈ order := (Finset.mem_sort _).mpr (Finset.mem_attach _ _)
    let visit : (child : ↥keys) → child ∈ order → Except ImportFault (Image hash (modes child).kind) := fun child _ => do
      if !Dasl.validByteComponent child.val then throw (.component child.val)
      if modes child = .gitlink then throw (.gitlink child.val)
      stage hash (children child)
    let visitCid : (child : ↥keys) → child ∈ order → Except ImportFault Cid := fun child _ => do
      if !Dasl.validByteComponent child.val then throw (.component child.val)
      if modes child = .gitlink then throw (.gitlink child.val)
      rootCid hash (children child)
    have runTree : stage hash (.tree keys modes children) = (do
        let read ← Translate.Graph.scan order visit
        let images := fun child => read child (member child)
        let root ← stageDirectory hash (namedDirectory modes fun child => (images child).name)
        pure (treeImage root images)) := by rw [stage]; rfl
    have runCid : rootCid hash (.tree keys modes children) = (do
        let read ← Translate.Graph.scan (Value := fun _ : ↥keys => Cid) order visitCid
        directoryCid hash (namedDirectory modes fun child => read child (member child))) := by rw [rootCid]; rfl
    have visits : visitCid = fun child hit => (visit child hit).map Image.name := by
      funext child hit
      by_cases valid : Dasl.validByteComponent child.val = true <;> by_cases localMode : modes child = .gitlink <;>
        simp [visitCid, visit, valid, localMode, ih, throw, throwThe, Except.map, Bind.bind, Except.bind] <;> rfl
    rw [runTree, runCid, visits, scan_map (fun (child : ↥keys) (image : Image hash (modes child).kind) => image.name)]
    cases Translate.Graph.scan order visit with
    | error fault => rfl
    | ok read =>
      let images := fun child => read child (member child)
      change directoryCid hash (namedDirectory modes fun child => (images child).name) = Except.map Image.name
        (stageDirectory hash (namedDirectory modes fun child => (images child).name) >>= fun root =>
          Except.ok (treeImage root images))
      rw [directoryCid_eq_stageDirectory]
      generalize stageDirectory hash (namedDirectory modes fun child => (images child).name) = made
      cases made <;> rfl

theorem accounted (image : Image hash kind) (keep : Cid → Bool) {binding : Cid × ByteArray}
    (member : binding ∈ image.writes) : binding ∈ image.retained keep ∨ binding.1 ∈ image.promised keep := by
  by_cases kept : keep binding.1 = true
  · exact .inl (List.mem_filter.mpr ⟨member, kept⟩)
  · exact .inr (List.mem_map.mpr ⟨binding, List.mem_filter.mpr ⟨member, by simpa using kept⟩, rfl⟩)

theorem publishRetained_of_publish {image : Image hash kind} {before full : Cid → Option ByteArray}
    (published : image.publish before = .ok full) (keep : Cid → Bool) :
    ∃ part, image.publishRetained keep before = .ok part ∧ Naming.Subset (Naming.graph part) (Naming.graph full) := by
  have whole : Naming.Binding (Naming.union (Naming.graph before) (Naming.listed image.writes)) :=
    (Naming.admit_exists_iff before image.writes).mp ⟨full, published⟩
  have smaller : Naming.Subset (Naming.union (Naming.graph before) (Naming.listed (image.retained keep)))
      (Naming.union (Naming.graph before) (Naming.listed image.writes)) := by
    rintro name bytes (old | kept)
    · exact .inl old
    · exact .inr (List.mem_filter.mp kept).1
  obtain ⟨part, accepted⟩ := (Naming.admit_exists_iff before (image.retained keep)).mpr
    (fun _ _ _ first second => whole (smaller first) (smaller second))
  refine ⟨part, accepted, ?_⟩
  rw [Naming.admit_eq_union accepted, Naming.admit_eq_union published]
  exact smaller

theorem readVerified_ofPartial {part full : Cid → Option ByteArray} {promised : List Cid} {lane : CasLane}
    {name : Cid} {bytes : ByteArray} (subset : Naming.Subset (Naming.graph part) (Naming.graph full))
    (found : readVerified hash (Store.ofPartial part promised) lane name = .found bytes) :
    readVerified hash (Store.ofPublished full) lane name = .found bytes := by
  obtain ⟨seen, addressed⟩ := readVerified_found found
  by_cases tagged : laneMatches lane name = true
  · cases held : part name with
    | none => by_cases owed : name ∈ promised <;> simp [Store.ofPartial, tagged, held, owed] at seen
    | some wire =>
      have exact : wire = bytes := by simpa [Store.ofPartial, tagged, held] using seen
      have kept : full name = some bytes := subset (exact ▸ held)
      simp [readVerified, Store.ofPublished, Read.andThen, tagged, kept, addressed]
  · simp [Store.ofPartial, tagged] at seen

theorem lookupChildRouted_partial_sound {directory : ByteDirectory} {image : Image hash .tree}
    {full part : Cid → Option ByteArray} {promised : List Cid} {fuel : Nat} {key : ByteKey}
    {result : Option (Entry Cid)} (staged : image.OfDirectory directory) (bounds : DirectoryBounds hash directory)
    (covered : image.Covered full) (subset : Naming.Subset (Naming.graph part) (Naming.graph full))
    (checked : lookupChildRouted hash (Store.ofPartial part promised) fuel image.name key = .ok result) :
    directory.ordered.lookup? key = result := by
  let reader := dirRead hash (.ofPublished full)
  let built := build policy directory.ordered
  let name := replayAddress (dirProfile hash).nameBlock? image.name
  let reference : Silmaril.Formats.Dasl.Store Cid := ⟨fun name value => reader name = .found value, fun _ _ => False⟩
  have stored : Stored dirCodec name built reference := by
    intro block member
    obtain ⟨wire, rendered, addressed, included⟩ := staged.2 block member
    have tag := laneMatches_address hash .object image.bytes
    obtain ⟨value, encoded, encodable⟩ := (bounds image.name tag block member).encode
    obtain ⟨serialize, parse⟩ := bdasl_roundtrip value encodable
    have exactWire : wire = (Silmaril.Formats.Dasl.Wire.canonicalBdaslModel value).encode.toByteArray := by
      apply Option.some.inj
      simpa only [blockBytes?, encoded, Option.bind_some, serialize] using rendered.symm
    have fetches : full (name block) = some wire := covered _ included
    refine ⟨value, encoded, ?_⟩
    change reader (name block) = .found value
    change name block = address hash .object wire at addressed
    rw [addressed] at fetches ⊢
    have verified : readVerified hash (Store.ofPublished full) .object (address hash .object wire) = .found wire := by
      simp [readVerified, Store.ofPublished, Read.andThen, fetches]
    have decoded : Profile.bdasl.parse? wire = some value := by rw [exactWire]; exact parse
    simp [reader, dirRead, verified, decoded]
  have binding : reference.Binding :=
    ⟨fun _ _ _ first second => by
      have same := first.symm.trans second
      cases same; rfl, fun _ _ _ impossible => impossible.elim⟩
  have sound : Silmaril.Formats.Dasl.Prolly.Read.Sound (dirRead hash (Store.ofPartial part promised)) reference := by
    intro cid value found
    change dirRead hash (.ofPublished full) cid = .found value
    unfold dirRead at found ⊢
    cases seen : readVerified hash (Store.ofPartial part promised) .object cid with
    | found bytes =>
      rw [seen] at found
      rw [readVerified_ofPartial subset seen]
      exact found
    | _ => rw [seen] at found; cases found
  have exactName : built.rootName name = image.name := staged.1
  rw [← exactName] at checked
  exact lookupChildRouted_sound stored binding sound checked

end Silmaril.Proofs.Formats.Git.Filesystem
