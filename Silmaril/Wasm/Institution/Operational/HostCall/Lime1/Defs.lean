module

public import Silmaril.Wasm.Lime1.Execution.Callout
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1

open Execution.Runtime (EvalCtx Frame FuncAddr FuncInst MemAddr MemInst ModuleInst Result Value)
open Wasm.Lime1.Execution

/-- The designated memory is allocated in the base store. Its live byte array
may change, while its extent, declared limit and all other allocations stay fixed. -/
structure Memory32 {H : Type} (base : Store H) where
  address : MemAddr
  initial : MemInst
  allocated : base.memories[address.value]? = some initial

namespace Memory32

def store {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Store H :=
  setMemory base memory.address { memory.initial with data := bytes }

def Live {H : Type} {base : Store H} (memory : Memory32 base) (bytes : ByteArray) : Prop :=
  bytes.size = memory.initial.data.size

end Memory32

/-- An allocated host target and its complete ordered numeric signature. -/
structure Site (H : Type) where
  address : FuncAddr
  type : Wasm.Lime1.FuncType
  code : H

def Site.Allocated {H : Type} (site : Site H) (base : Store H) : Prop :=
  base.funcs[site.address.value]? = some (.host site.type site.code)

def Site.Arguments {H : Type} (site : Site H) (args : List Value) : Prop :=
  args.map Value.type = site.type.params

def Site.TypedResult {H : Type} (site : Site H) : Result → Prop
  | .values vs => vs.map Value.type = site.type.results
  | .trap => True

/-- The embedding must reestablish the live store relation on every returned
outcome from this site with typed operands, including a returned trap. -/
def Site.Contract {H : Type} {base : Store H} (site : Site H) (memory : Memory32 base)
    (host : HostSemantics H) : Prop :=
  ∀ ⦃bytes args returned outcome⦄, memory.Live bytes → site.Arguments args →
    host site.code (memory.store bytes) args (.returned returned outcome) →
    ∃ next, memory.Live next ∧ returned = memory.store next ∧ site.TypedResult outcome

def Site.callout {H : Type} (site : Site H) (context : EvalCtx Wasm.Lime1.Instr) (args : List Value) :
    Execution.Runtime.Callout H Wasm.Lime1.Instr :=
  ⟨context, site.address, site.type, site.code, args⟩

def Site.pending {H : Type} (site : Site H) (s : Store H) (outer : Frame)
    (context : EvalCtx Wasm.Lime1.Instr) (args : List Value) : Config H :=
  ⟨s, outer, context.plug value (values args ++ [.invoke site.address])⟩

abbrev IndirectSite := CallResolution.Indirect.Site

/-- The consulted table and expected type are fixed in the active module and
base store. All nonnull entries are allocated. Matching entries denote hosts. -/
structure IndirectSite.Linked {H : Type} (site : IndirectSite) (base : Store H)
    (module : ModuleInst) : Prop where
  tableAt : frameTable base ⟨[], module⟩ = some site.table
  signatureAt : module.types[site.typeIndex.toNat]? = some site.signature
  entries : ∀ address, some address ∈ site.table.refs →
    ∃ fn : FuncInst Wasm.Lime1.Func H, base.funcs[address.value]? = some fn ∧
      (fn.type = site.signature → ∃ code, fn = .host site.signature code)

/-- Each matching, allocated target supplies the ordinary host contract. -/
def IndirectSite.Contract {H : Type} {base : Store H} (site : IndirectSite) (memory : Memory32 base)
    (host : HostSemantics H) : Prop :=
  ∀ address code, some address ∈ site.table.refs →
    (⟨address, site.signature, code⟩ : Site H).Allocated base →
    (⟨address, site.signature, code⟩ : Site H).Contract memory host

/-- A single native lookup supplies an allocated host or one of the three
trap witnesses. The selector is the unsigned i32 table index. -/
inductive IndirectSite.Lookup {H : Type} (site : IndirectSite) (base : Store H) (selector : BitVec 32) :
    Option (Site H) → Prop where
  | bounds (entry : site.table.refs[selector.toNat]? = none) : site.Lookup base selector none
  | null (entry : site.table.refs[selector.toNat]? = some none) : site.Lookup base selector none
  | mismatch {address : FuncAddr} {fn : FuncInst Wasm.Lime1.Func H}
      (entry : site.table.refs[selector.toNat]? = some (some address))
      (allocated : base.funcs[address.value]? = some fn) (different : fn.type ≠ site.signature) :
      site.Lookup base selector none
  | host {address : FuncAddr} {code : H}
      (entry : site.table.refs[selector.toNat]? = some (some address))
      (allocated : (⟨address, site.signature, code⟩ : Site H).Allocated base) :
      site.Lookup base selector (some ⟨address, site.signature, code⟩)

def IndirectSite.lookupHead {H : Type} : Option (Site H) → Admin
  | some target => .invoke target.address
  | none => .trap

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1
