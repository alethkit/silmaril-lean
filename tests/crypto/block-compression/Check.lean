module

import Silmaril.Crypto.BlockCompression.SHA256.Thms
import Silmaril.Crypto.HashFns.Defs
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Silmaril.Crypto
open Lean Elab Command

private def ascending : SHA256.OctetBlock := Vector.ofFn fun i => UInt8.ofNat i.val

example : (SHA256.parseBlock ascending.toList).head? = some 0x00010203 := by
  decide +kernel

example : (HashFn.sha256.digestVector [0x61, 0x62, 0x63]).toList = SHA256.digest [0x61, 0x62, 0x63] :=
  HashFn.digestVector_toList _ _

run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for decl in [``BlockCompressor.chain_append, ``BlockCompressor.chain_commutes,
      ``HashFn.digestVector_toList, ``SHA256.octetBlock_words,
      ``SHA256.octetCompressors_step, ``SHA256.octetCompressors_chain] do
    let axioms ← collectAxioms decl
    for name in axioms do
      unless allowed.contains name do
        throwError "{decl} transitively uses {name}"
    logInfo m!"{decl} transitive axioms {axioms.toList}"
