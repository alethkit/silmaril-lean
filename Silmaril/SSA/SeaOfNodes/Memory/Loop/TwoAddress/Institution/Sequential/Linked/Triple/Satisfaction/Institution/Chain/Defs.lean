module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Chain.Defs

/-! Staged re-emission in the existing generated linked-triple rooms. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open Linked.Satisfaction.ReductImage (CaptureChain)
open Memory.Diamond.Institution renaming Signature → EntrySignature

/-- Re-emit along each typed capture map in source-to-target order. -/
def Sentence.mapChain : {P Q : EntrySignature} → CaptureChain P Q → Sentence P → Sentence Q
  | _, _, .nil _, sentence => sentence
  | _, _, .cons head tail, sentence => (sentence.map head).mapChain tail

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction
