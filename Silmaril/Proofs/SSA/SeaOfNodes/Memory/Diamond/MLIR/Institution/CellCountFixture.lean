module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs

/-! The same pair of swaps at the two-cell and finite-cell boundaries. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountFixture

open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Equation → NativeEquation
open RVSDG (Port Tuple)

def sig : EntrySignature := ⟨[.address, .address, .address, .word]⟩

def a : Port sig.args .address := .head
def b : Port sig.args .address := .tail .head
def c : Port sig.args .address := .tail (.tail .head)

def prependSwap {past : List (List ValueSort)} {version : Nat}
    (left right : Port sig.args .address)
    (rest : Memory.Body sig.args ([.word] :: [.word] :: past) (version + 2)) :
    Memory.Body sig.args past version :=
  .load (.latest version) (.arg left)
    (.load (.latest version) (.arg right)
      (.store (.latest version) (.arg left) (.output ⟨0, by simp⟩ .head)
        (.store (.latest (version + 1)) (.arg right) (.output ⟨1, by simp⟩ .head) rest)))

def finish {past : List (List ValueSort)} : Memory.Body sig.args past 4 :=
  .ret (.latest 4) (.arg (.tail (.tail (.tail .head))))

def diamond (body : Memory.Graph sig.args) : Graph sig.args :=
  ⟨⟨.onTrue⟩, fun _ => body, .ret (.latest 0) (.arg .head)⟩

def commuteSwaps : NativeEquation sig :=
  ⟨diamond (prependSwap a b (prependSwap b c finish)),
    diamond (prependSwap b c (prependSwap a b finish))⟩

def threeInputs : Tuple (Val 3) sig.args :=
  .cons (0 : Address 3) (.cons (1 : Address 3) (.cons (2 : Address 3) (.cons (0 : Word) .nil)))

def threeHeap : Heap 3 := fun address => BitVec.ofNat 64 address.val

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountFixture
