module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
import Silmaril.Proofs.Formats.Dasl.ProllyScan

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block Policy build)

variable {Name Key Payload : Type}

theorem Read.Sound.mono {read : Read Name} {store extension : Store Name}
    (sound : Read.Sound read store) (incl : store.Subset extension) : Read.Sound read extension :=
  fun _ _ hit => incl.1 (sound hit)

theorem closedMap_sound [LinearOrder Key] {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    (policy : Policy Key) {map : OrderedMap Key Payload} {address : Block Name Key Payload → Name} {store : Store Name}
    (stored : Stored codec address (build policy map) store) (bound : store.Binding) {read : Read Name}
    (sound : Read.Sound read store) {fuel : Nat} {found : OrderedMap Key Payload}
    (checked : closedMap codec read policy.width fuel ((build policy map).rootName address) = .ok found) :
    map = found :=
  Proofs.Formats.Dasl.ProllyScan.closed_map_sound policy stored bound sound checked

/-- Both positive and negative answers are correct against every binding reference
including the reader and the canonical encoding. Name uniqueness is not needed. -/
theorem lookup_sound [LinearOrder Key] {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    (policy : Policy Key) {map : OrderedMap Key Payload} {address : Block Name Key Payload → Name} {store : Store Name}
    (stored : Stored codec address (build policy map) store) (bound : store.Binding) {read : Read Name}
    (sound : Read.Sound read store) {fuel : Nat} {key : Key} {result : Option Payload}
    (checked : lookup codec read policy.width fuel ((build policy map).rootName address) key = .ok result) :
    map.lookup? key = result :=
  Proofs.Formats.Dasl.ProllyScan.lookup_sound policy stored bound sound checked

end Silmaril.Formats.Dasl.Prolly
