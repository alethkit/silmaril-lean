module

public import Silmaril.Formats.Dasl.Prolly.Range.Defs
import Silmaril.Formats.Dasl.Prolly.Scan.Thms
import Silmaril.Semantics.Prolly.Routing.Thms
import Silmaril.Semantics.OrderedMap.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyRange

public section

namespace Silmaril.Formats.Dasl.Prolly.Range

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block Node Policy blockOccurrences build flatten nodeBlock)

variable {Name Key Payload : Type} [LinearOrder Key]

theorem mapSlice_lookup (lower upper : Key) (map : OrderedMap Key Payload) (key : Key) (payload : Payload) :
    (mapSlice lower upper map).lookup? key = some payload ↔
      map.lookup? key = some payload ∧ lower ≤ key ∧ key < upper := by
  rw [OrderedMap.lookup_eq_some_iff, OrderedMap.lookup_eq_some_iff]
  simp [mapSlice, includes, List.mem_filter]

theorem scan_sound {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (width : Nat) (lower upper : Key)
    (fuel level : Nat) (node : Node Key Payload level)
    (ordered : (flatten level node).Pairwise fun left right => left.1 < right.1)
    (separators : Node.Separators level node)
    (agrees : ∀ block ∈ blockOccurrences address level node,
      ∀ actual, read (address block) = .ok actual → actual = block)
    {expected : Option Nat} {result : Result Key Payload}
    (checked : scan read width lower upper fuel expected (address (nodeBlock address level node)) = .ok result) :
    result = ⟨(flatten level node).filter fun entry => includes lower upper entry.1, selectedVisits lower level node⟩ :=
  Proofs.Formats.Dasl.ProllyRange.range_scan_sound address width lower upper fuel level node ordered separators agrees checked

theorem visits_le_all (address : Block Name Key Payload → Name) (lower : Key) (level : Nat)
    (node : Node Key Payload level) : selectedVisits lower level node ≤ (blockOccurrences address level node).length :=
  Proofs.Formats.Dasl.ProllyRange.visits_le_all address lower level node

/-- Every successful named scan agrees with each stored routable reference in
a binding extension containing its observed reads. No condition on omitted reads. -/
theorem scan_stored_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {read : Read Name} {tree : Semantics.Prolly.Tree Key Payload} {address : Block Name Key Payload → Name} {store : Store Name}
    (routable : tree.Routable) (stored : Stored codec address tree store) (bound : store.Binding)
    (sound : Read.Sound read store) {width fuel : Nat} {lower upper : Key} {result : Result Key Payload}
    (checked : scan (readBlock codec read) width lower upper fuel none (tree.rootName address) = .ok result) :
    result = ⟨tree.entries.filter fun entry => includes lower upper entry.1,
      selectedVisits lower tree.level tree.root⟩ :=
  scan_sound address width lower upper fuel tree.level tree.root routable.1 routable.2
    (fun _ member _ hit => readBlock_sound stored bound sound member hit) checked

theorem scan_build_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    (policy : Policy Key) (map : OrderedMap Key Payload) {read : Read Name}
    {address : Block Name Key Payload → Name} {store : Store Name}
    (stored : Stored codec address (build policy map) store) (bound : store.Binding) (sound : Read.Sound read store)
    {fuel : Nat} {lower upper : Key} {result : Result Key Payload}
    (checked : scan (readBlock codec read) policy.width lower upper fuel none ((build policy map).rootName address) = .ok result) :
    result.entries = (mapSlice lower upper map).entries := by
  have exactResult := scan_stored_sound (Semantics.Prolly.build_routable policy map) stored bound sound checked
  simpa [mapSlice, Semantics.Prolly.build_entries] using congrArg Result.entries exactResult

end Silmaril.Formats.Dasl.Prolly.Range
