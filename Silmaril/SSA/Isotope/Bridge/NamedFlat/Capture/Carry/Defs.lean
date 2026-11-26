module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms
public import Silmaril.SSA.Isotope.LetCase.Thms

/-! # Carry a selected ambient slot in the actual internal packets -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry

open LambdaSSA (FiniteCFG Flat)
open LetCase.LocallyNameless (Tm)

universe u v

variable {F : Type v} {blocks exits n : Nat}

/-- Rename operands while pairing each internal jump argument with the
selected value. Outward payloads keep their original shape and order. -/
def body : {m k : Nat} → Flat F (blocks + exits) m → (Fin m → Fin k) → Fin k → Flat F (blocks + exits) k
  | _, _, .br i a, rename, slot =>
    .br i (Fin.addCases (fun _ => .pair (a.rename rename) (.bv slot)) (fun _ => a.rename rename) i)
  | _, _, .let₁ a tail, rename, slot => .let₁ (a.rename rename) (body tail (Tm.up rename) slot.succ)
  | _, _, .let₂ a tail, rename, slot => .let₂ (a.rename rename) (body tail (Tm.up (Tm.up rename)) slot.succ.succ)
  | _, _, .case a l r, rename, slot =>
    .case (a.rename rename) (body l (Tm.up rename) slot.succ) (body r (Tm.up rename) slot.succ)

/-- In a decoded row, the old argument is at one and the carried slot is at
zero. Other older indices still refer to their original caller slots. -/
def decodedIndex (slot : Fin n) : Fin (n + 1) → Fin (n + 3) :=
  Fin.cases 1 fun i => if i = slot then 0 else i.succ.succ.succ

/-- The caller context and all label positions stay the same. Only internal
packets and the scope immediately under their decoders change. -/
def graph (g : FiniteCFG F blocks exits n) (slot : Fin n) : FiniteCFG F blocks exits n :=
  ⟨body g.entry id slot, fun i => .let₂ (.bv 0) (body (g.block i) (decodedIndex slot) 0)⟩

variable {τ : Type u} [HasProduct τ]

def packetTypes (R : Fin blocks → τ) (β : BoundCtx τ n) (slot : Fin n) : Fin blocks → τ :=
  fun i => product (R i) (β.get slot)

end Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
