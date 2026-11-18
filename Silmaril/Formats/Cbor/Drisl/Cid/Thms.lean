module

public import Silmaril.Formats.Cbor.Drisl.Cid.Defs

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

theorem Cid.parse_bytes (profile : CidProfile) (cid : Cid profile) :
    (Cid.codec profile).parse? ((Cid.codec profile).bytes cid) = some cid := by
  simp [Cid.codec, cid.property]

theorem CidCodec.read_render {Link : Type} (codec : CidCodec Link)
    (inverse : ∀ cid, codec.parse? (codec.bytes cid) = some cid) (cid : Link) :
    codec.read? (codec.render cid) = some cid := by
  simp [CidCodec.read?, CidCodec.render, inverse]

theorem Cid.read_render (profile : CidProfile) (cid : Cid profile) :
    (Cid.codec profile).read? ((Cid.codec profile).render cid) = some cid :=
  CidCodec.read_render _ (Cid.parse_bytes profile) cid

end Silmaril.Formats.Cbor.Drisl
