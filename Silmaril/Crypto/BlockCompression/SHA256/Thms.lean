module

public import Silmaril.Crypto.BlockCompression.Thms
public import Silmaril.Crypto.BlockCompression.SHA256.Defs

public section
namespace Silmaril.Crypto.SHA256

theorem octetBlock_words (block : OctetBlock) : (parseBlock block.toList).length = 16 := by
  simp [parseBlock_length]

theorem octetCompressors_step (state : State) (block : OctetBlock) :
    kernelOctetCompressor.step state.toInitHash block =
      (octetCompressor.step state block).toInitHash := by
  have back (s : Kernel.InitHash) : s.toState.toInitHash = s := by cases s; rfl
  simp only [octetCompressor, kernelOctetCompressor, processBlock_eq_compressBlock, back]

theorem octetCompressors_chain (state : State) (blocks : List OctetBlock) :
    kernelOctetCompressor.chain state.toInitHash blocks =
      (octetCompressor.chain state blocks).toInitHash :=
  BlockCompressor.chain_commutes octetCompressor kernelOctetCompressor State.toInitHash
    octetCompressors_step state blocks

end Silmaril.Crypto.SHA256
