module

public import Silmaril.Elf.Staged.Pinned.ZlibLibz1211.Resolver.Defs
public import Silmaril.Elf.Staged.Pinned.ZlibLibz1211.Thms
import Silmaril.Elf.Facts.Thms

/-! # Versioned lookup and code for the pinned `crc32_z` resolver -/

@[expose] public section

namespace Silmaril.Elf.Staged.Pinned.ZlibLibz1211

open Silmaril.Elf Silmaril.Elf.Staged.Reader

/-- The pinned file's versioned lookup resolves `crc32_z` to the IFUNC entry. -/
theorem crc32z_lookup : Lookup F crc32zSelector (some crc32zResolver) :=
  ⟨_, parses, by decide +kernel⟩

/-- The executable segment holds the resolver bytes, whose length agrees with `st_size`. -/
theorem crc32z_resolver_code :
    CodeAt F crc32zResolver.value crc32zResolverBytes ∧
      crc32zResolverBytes.length = crc32zResolver.size :=
  ⟨codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel), rfl⟩

/-- Treating this versioned IFUNC reference as a plain function binding is invalid. -/
theorem crc32z_not_binds (v : Nat) (code : List (BitVec 8)) : ¬ Binds F crc32zSelector v code :=
  fun h =>
    let ⟨_, lookup, _, plain, _⟩ := h.lookup
    Bool.noConfusion ((congrArg Def.ifunc (Option.some.inj (crc32z_lookup.unique lookup))).trans plain)

end Silmaril.Elf.Staged.Pinned.ZlibLibz1211
