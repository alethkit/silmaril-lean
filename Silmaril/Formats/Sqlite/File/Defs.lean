module
public import Silmaril.Formats.Sqlite.Defs

/-! SQLite's persistent database page array. Views share the original
ByteArray; extracting a copy is an explicit `materialize` operation. Journal
and WAL files are distinct formats and are not interpreted as database pages. -/
@[expose] public section
namespace Silmaril.Formats.Sqlite.File

structure View where
  source : Bytes
  start : Nat
  length : Nat
  bounded : start + length ≤ source.length

namespace View
def ofBytes (bytes : Bytes) : View := ⟨bytes, 0, bytes.length, by omega⟩
def get? (view : View) (offset : Nat) : Option UInt8 :=
  if offset < view.length then view.source.data[view.start + offset]? else none
def sub? (view : View) (offset count : Nat) : Option View :=
  if h : offset + count ≤ view.length then
    some ⟨view.source, view.start + offset, count, by have := view.bounded; omega⟩
  else none
def materialize (view : View) : Bytes :=
  ⟨view.source.data.extract view.start (view.start + view.length)⟩
def be? (view : View) (offset width : Nat) : Option Nat :=
  (List.range width).foldlM (fun acc i => do
    pure (acc * 256 + (← view.get? (offset + i)).toNat)) 0
def le? (view : View) (offset width : Nat) : Option Nat :=
  (List.range width).foldlM (fun acc i => do
    pure (acc + (← view.get? (offset + i)).toNat * 256^i)) 0
end View

/-- An initialized but schema-less database can retain the zero encoding
sentinel. It does not license interpreting a text payload with an encoding. -/
inductive TextEncoding where | unspecified | utf8 | utf16le | utf16be
  deriving DecidableEq, Repr

def TextEncoding.ofNat? : Nat → Option TextEncoding
  | 0 => some .unspecified | 1 => some .utf8
  | 2 => some .utf16le | 3 => some .utf16be | _ => none

structure Header where
  pageSize : Nat
  writeVersion : Nat
  readVersion : Nat
  reserved : Nat
  changeCounter : Nat
  rawPageCount : Nat
  freelistTrunk : Nat
  freelistCount : Nat
  schemaCookie : Nat
  schemaFormat : Nat
  cacheSize : Int
  largestRoot : Nat
  encoding : TextEncoding
  userVersion : Nat
  incrementalVacuum : Bool
  applicationId : Nat
  versionValidFor : Nat
  sqliteVersion : Nat
  deriving DecidableEq, Repr

def Header.usableSize (header : Header) : Nat := header.pageSize - header.reserved
def Header.pageCountValid (header : Header) : Bool :=
  header.rawPageCount != 0 && header.changeCounter == header.versionValidFor
def Header.autoVacuum (header : Header) : Bool := header.largestRoot != 0
def Header.writable (header : Header) : Bool := header.writeVersion == 1 || header.writeVersion == 2

def signed (width value : Nat) : Int :=
  if value < 2^(8*width-1) then value else (value : Int) - (2^(8*width) : Nat)

def headerMagic : List UInt8 := [83,81,76,105,116,101,32,102,111,114,109,97,116,32,51,0]
def validPageSize (size : Nat) : Bool :=
  [512,1024,2048,4096,8192,16384,32768,65536].contains size

def parseHeader? (source : Bytes) : Option Header := do
  let view := View.ofBytes source
  if source.length < 100 then none else do
    if !(List.range 16).all (fun i => view.get? i == headerMagic[i]?) then none else do
      let encoded ← view.be? 16 2
      let pageSize := if encoded == 1 then 65536 else encoded
      let writeVersion ← view.be? 18 1
      let readVersion ← view.be? 19 1
      let reserved ← view.be? 20 1
      if !validPageSize pageSize || writeVersion == 0 ||
          !(readVersion == 1 || readVersion == 2) || pageSize - reserved < 480 then none else do
        if (← view.be? 21 1) != 64 || (← view.be? 22 1) != 32 ||
            (← view.be? 23 1) != 32 then none else do
          if !(List.range 20).all (fun i => view.get? (72+i) == some 0) then none else do
            let schemaFormat ← view.be? 44 4
            let encoding ← TextEncoding.ofNat? (← view.be? 56 4)
            let largestRoot ← view.be? 52 4
            let incremental ← view.be? 64 4
            if schemaFormat > 4 || (encoding == .unspecified && schemaFormat != 0) ||
                (largestRoot == 0 && incremental != 0) then none else do
              pure {
                pageSize := pageSize, writeVersion := writeVersion, readVersion := readVersion, reserved := reserved,
                changeCounter := (← view.be? 24 4), rawPageCount := (← view.be? 28 4),
                freelistTrunk := (← view.be? 32 4), freelistCount := (← view.be? 36 4),
                schemaCookie := (← view.be? 40 4), schemaFormat := schemaFormat,
                cacheSize := signed 4 (← view.be? 48 4), largestRoot := largestRoot,
                encoding := encoding,
                userVersion := (← view.be? 60 4), incrementalVacuum := incremental != 0,
                applicationId := (← view.be? 68 4), versionValidFor := (← view.be? 92 4),
                sqliteVersion := (← view.be? 96 4) }

/-- Header page count is authoritative only with its matching change counter;
otherwise SQLite derives the count from physical file size. Trailing complete
pages may exist beyond the authoritative logical page count. -/
structure Image where
  source : Bytes
  header : Header
  pageCount : Nat
  physicalPageCount : Nat

def parse? (source : Bytes) : Option Image := do
  let header ← parseHeader? source
  if source.length % header.pageSize != 0 then none else do
    let physicalPageCount := source.length / header.pageSize
    let pageCount := if header.pageCountValid then header.rawPageCount else physicalPageCount
    if pageCount == 0 || pageCount > physicalPageCount || physicalPageCount > 4294967294 ||
        header.freelistCount > pageCount || header.freelistTrunk > pageCount ||
        header.largestRoot > pageCount then none else
      some ⟨source, header, pageCount, physicalPageCount⟩

/-- SQLite also recognizes a zero-byte file as an uninitialized empty database.
It has no header, pages, encoding or schema cookie until first initialization. -/
inductive DatabaseFile where
  | empty
  | initialized (image : Image)

def read? (source : Bytes) : Option DatabaseFile :=
  if source.length == 0 then some .empty else DatabaseFile.initialized <$> parse? source

def Image.page? (image : Image) (number : Nat) : Option View :=
  if number == 0 || number > image.pageCount then none else
    (View.ofBytes image.source).sub? ((number-1)*image.header.pageSize) image.header.pageSize
def Image.usablePage? (image : Image) (number : Nat) : Option View := do
  (← image.page? number).sub? 0 image.header.usableSize

/-- Materialize only an array of shared views, without copying page payloads. -/
def Image.pages? (image : Image) : Option (Array View) :=
  ((List.range image.pageCount).mapM (fun i => image.page? (i+1))).map List.toArray

/-- SQLite's pending-byte lock page is never a b-tree, freelist or pointer-map
page, although its position is included in page numbering. -/
def Header.lockPage (header : Header) : Nat := 0x40000000 / header.pageSize + 1

/-- Pointer-map pages are spaced by usable-size/5+1, skipping the pending-byte
page. Page one has no pointer-map entry. -/
def pointerMapPage (header : Header) (page : Nat) : Nat :=
  if page < 2 then 0 else
    let stride := header.usableSize / 5 + 1
    let candidate := (page-2)/stride*stride+2
    if candidate == header.lockPage then candidate+1 else candidate

def Header.isPointerMapPage (header : Header) (page : Nat) : Bool :=
  header.autoVacuum && page ≥ 2 && pointerMapPage header page == page

inductive PageRole where
  | btree | overflow | freelistTrunk | freelistLeaf | pointerMap | lockByte
  deriving DecidableEq, Repr

structure FreelistTrunk where
  next : Nat
  leaves : Array Nat
  deriving DecidableEq, Repr

def parseFreelistTrunk? (image : Image) (number : Nat) : Option FreelistTrunk := do
  if number < 2 || number == image.header.lockPage || image.header.isPointerMapPage number then none else do
  let page ← image.usablePage? number
  let next ← page.be? 0 4
  let count ← page.be? 4 4
  if next > image.pageCount || count > page.length/4-2 then none else do
    let leaves ← (List.range count).mapM (fun i => page.be? (8+4*i) 4)
    if leaves.any (fun p => p < 2 || p > image.pageCount || p == number || p == image.header.lockPage || image.header.isPointerMapPage p)
      then none else some ⟨next, leaves.toArray⟩

structure Freelist where
  trunks : List Nat
  leaves : List Nat
  deriving DecidableEq, Repr

def freelistAux? (image : Image) : Nat → Nat → List Nat → List Nat → Option Freelist
  | _, 0, trunks, leaves => some ⟨trunks.reverse, leaves.reverse⟩
  | 0, _+1, _, _ => none
  | fuel+1, number, trunks, leaves => do
    if (trunks ++ leaves).contains number then none else do
      let trunk ← parseFreelistTrunk? image number
      let newLeaves := trunk.leaves.toList
      if !decide (newLeaves ++ number :: trunks ++ leaves).Nodup then none else
        freelistAux? image fuel trunk.next (number :: trunks) (newLeaves.reverse ++ leaves)

def freelist? (image : Image) : Option Freelist := do
  let result ← freelistAux? image image.pageCount image.header.freelistTrunk [] []
  if result.trunks.length + result.leaves.length == image.header.freelistCount then some result else none

inductive PointerKind where
  | root | free | firstOverflow | nextOverflow | btreeChild
  deriving DecidableEq, Repr

def PointerKind.ofNat? : Nat → Option PointerKind
  | 1 => some .root | 2 => some .free | 3 => some .firstOverflow
  | 4 => some .nextOverflow | 5 => some .btreeChild | _ => none

structure PointerEntry where
  kind : PointerKind
  parent : Nat
  deriving DecidableEq, Repr

def pointerEntry? (image : Image) (page : Nat) : Option PointerEntry := do
  if !image.header.autoVacuum || page < 3 || page > image.pageCount || page == image.header.lockPage
    then none else do
      let mapPage := pointerMapPage image.header page
      if page ≤ mapPage then none else do
        let view ← image.usablePage? mapPage
        let offset := (page-mapPage-1)*5
        let kind ← PointerKind.ofNat? (← view.be? offset 1)
        let parent ← view.be? (offset+1) 4
        if parent > image.pageCount then none else
          match kind with
          | .root | .free => if parent == 0 then some ⟨kind,parent⟩ else none
          | _ => if parent == 0 then none else some ⟨kind,parent⟩
end Silmaril.Formats.Sqlite.File
