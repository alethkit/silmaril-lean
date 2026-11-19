module

public import Silmaril.Formats.Dasl.Prolly.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type}

/-- A profile fixes all choices used by the builder and by bottom-up naming.
The key order is supplied separately. `render?` may reject a shallow value. -/
structure RootProfile (Name Key Payload : Type) where
  policy : Policy Key
  key : Encode.TotalCodec Key (Shallow Name)
  payload : Encode.TotalCodec Payload (Shallow Name)
  render? : Shallow Name → Option ByteArray
  hash : ByteArray → Name

namespace RootProfile

def nameBlock? (profile : RootProfile Name Key Payload) (block : Block Name Key Payload) : Option Name :=
  ((encodeBlock profile.key profile.payload block).bind profile.render?).map profile.hash

def rootName? [LinearOrder Key] (profile : RootProfile Name Key Payload) (map : OrderedMap Key Payload) : Option Name :=
  (build profile.policy map).rootName? profile.nameBlock?

/-- Any ordered representation of the semantic lookup map may contribute a root,
but it must use the fixed builder, codecs and naming profile at every block. -/
def Roots [LinearOrder Key] (profile : RootProfile Name Key Payload) :
    Naming.Relation Name (Key → Option Payload) :=
  fun name lookup => ∃ (map : OrderedMap Key Payload) (address : Block Name Key Payload → Name),
    (∀ key, map.lookup? key = lookup key) ∧
    (build profile.policy map).Admits profile.nameBlock? address ∧ (build profile.policy map).rootName address = name

/-- Exactly the shallow object observations of this addressed tree. No raw/blob
bindings are contributed here. An unencodable block contributes no observation;
use `Tree.Admits` to ensure no such block occurs. -/
def observations (profile : RootProfile Name Key Payload) (tree : Semantics.Prolly.Tree Key Payload)
    (address : Block Name Key Payload → Name) : Store Name :=
  ⟨Naming.push (tree.observations address) (fun block value => encodeBlock profile.key profile.payload block = some value),
    fun _ _ => False⟩

end RootProfile
end Silmaril.Formats.Dasl.Prolly
