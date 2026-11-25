module

public import Silmaril.Crypto.BlockCompression.Defs
public import Silmaril.Crypto.SHA256.Equiv

@[expose] public section
namespace Silmaril.Crypto.SHA256

abbrev OctetBlock := Vector UInt8 64

/-- FIPS 180-4 big-endian block parsing followed by the public UInt32 compressor. -/
def octetCompressor : BlockCompressor State 64 where
  step state block := processBlock state (parseBlock block.toList)

/-- The same typed block boundary for the existing bit-vector compressor. -/
def kernelOctetCompressor : BlockCompressor Kernel.InitHash 64 where
  step state block := Kernel.compressBlock state ((parseBlock block.toList).map UInt32.toBitVec)

end Silmaril.Crypto.SHA256
