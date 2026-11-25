module

public import Init.Data.Vector.Lemmas
public import Silmaril.Crypto.Interface.Defs

/-! Fixed-size octet blocks threaded through an explicit chaining state.
A complete digest can still use the existing HashFn interface. -/
@[expose] public section
namespace Silmaril.Crypto

universe u

structure BlockCompressor (State : Type u) (blockLen : Nat) where
  step : State → Vector UInt8 blockLen → State

def BlockCompressor.chain {State : Type u} {blockLen : Nat}
    (compressor : BlockCompressor State blockLen) (initial : State)
    (blocks : List (Vector UInt8 blockLen)) : State :=
  blocks.foldl compressor.step initial

/-- Give the digest its declared length at the type boundary. -/
def HashFn.digestVector (algorithm : HashFn) (message : List UInt8) :
    Vector UInt8 algorithm.digestLen :=
  ⟨(algorithm.hash message).toArray, by simpa using algorithm.digest_length message⟩

end Silmaril.Crypto
