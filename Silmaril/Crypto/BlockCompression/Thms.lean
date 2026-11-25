module

public import Silmaril.Crypto.BlockCompression.Defs

public section
namespace Silmaril.Crypto

universe u v

theorem BlockCompressor.chain_append {State : Type u} {blockLen : Nat}
    (compressor : BlockCompressor State blockLen) (initial : State)
    (left right : List (Vector UInt8 blockLen)) :
    compressor.chain initial (left ++ right) =
      compressor.chain (compressor.chain initial left) right :=
  List.foldl_append

/-- A one-block state translation lifts to every finite sequence of blocks. -/
theorem BlockCompressor.chain_commutes {Left : Type u} {Right : Type v} {blockLen : Nat}
    (left : BlockCompressor Left blockLen) (right : BlockCompressor Right blockLen)
    (translate : Left → Right)
    (step : ∀ state block, right.step (translate state) block = translate (left.step state block))
    (initial : Left) (blocks : List (Vector UInt8 blockLen)) :
    right.chain (translate initial) blocks = translate (left.chain initial blocks) :=
  List.foldl_hom translate step

@[simp] theorem HashFn.digestVector_toList (algorithm : HashFn) (message : List UInt8) :
    (algorithm.digestVector message).toList = algorithm.hash message := by
  simp [HashFn.digestVector]

end Silmaril.Crypto
