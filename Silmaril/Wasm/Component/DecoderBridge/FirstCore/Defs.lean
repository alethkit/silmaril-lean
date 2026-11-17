module

public import Silmaril.Wasm.Component.DecoderBridge.Sim.Defs

/-!
# The reference half when the first core instantiation fails: the fragment

`Task.failRefWired` (`DecoderBridge.Sim.Defs`) asks that, on an import-wired binary, a failure
of IR core node `k` (the nodes before it ready, each a core engine run without host calls)
makes the reference machine trap. This module names the binaries on which its first case,
`k = 0`, is proved (`FirstCore.Thms`), by a decidable condition on the REF reading:

* `firstCore? r`: the definitions of `r` before its first core instantiation, that
  instantiation's module index and arguments, and the definitions after it;
* `preOk nf ncf pre`: the definitions before the first core instantiation are core modules,
  function types with primitive parameters and result, function imports, `canon lower` (no
  options) of a component function defined so far, and inline core instances of core functions
  defined so far (`nf` component functions and `ncf` core functions defined before them);
* `coreMods pre`: the core modules those definitions define, in order;
* `splitMod m`: the core module has no tags, memories, tables, data or element segments (the
  fragment of the relocation lemmas `Proofs.….Reference.ShiftStep`);
* `FirstCoreFrag r` (`firstCoreFrag r = true`): `r` has a core instantiation; the definitions
  before the first one satisfy `preOk 0 0`; and the module it instantiates exists, has **no
  imports** and is in the split fragment.

Both test binaries are in the fragment (`FirstCore.Thms`: `trap_firstCoreFrag`,
`starts_firstCoreFrag`); for `starts.wasm` the first instantiated module (`call1`) imports `f`,
so the fragment is satisfied there only through the failure of node `0`, which its IR run does
not have. Outside the fragment, and for `k ≥ 1`, `Task.failRefWired` stays open
(`Task.failRefWiredRest`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance

variable {M : Type}

/-- A value type with no type index (a primitive). -/
def vtPrim : Syntax.VT → Bool
  | .prim _ => true
  | .idx _ => false

/-- A function type whose parameters and result are primitives. -/
def funcTypePrim (ft : Syntax.FuncType) : Bool :=
  ft.params.all (fun p => vtPrim p.2) && ft.result.all vtPrim

/-- **The definitions allowed before the first core instantiation**, with `nf` component
functions and `ncf` core functions defined before them. -/
def preOk : Nat → Nat → List (Syntax.Definition M) → Bool
  | _, _, [] => true
  | nf, ncf, .coreModule _ :: ds => preOk nf ncf ds
  | nf, ncf, .type (.func ft) :: ds => funcTypePrim ft && preOk nf ncf ds
  | nf, ncf, .import_ _ (.func _) :: ds => preOk (nf + 1) ncf ds
  | nf, ncf, .canon (.lower g []) :: ds => decide (g < nf) && preOk nf (ncf + 1) ds
  | nf, ncf, .coreInstance (.exports items) :: ds =>
    items.all (fun p => p.2.sort == .func && decide (p.2.idx < ncf)) && preOk nf ncf ds
  | _, _, _ :: _ => false

/-- The core modules a list of definitions defines, in order. -/
def coreMods : List (Syntax.Definition M) → List M
  | [] => []
  | .coreModule m :: ds => m :: coreMods ds
  | _ :: ds => coreMods ds

/-- The definitions before the first core instantiation, its module index and arguments, and
the definitions after it. -/
def firstCore? : List (Syntax.Definition M) →
    Option (List (Syntax.Definition M) × Nat × List (String × Nat) × List (Syntax.Definition M))
  | [] => none
  | .coreInstance (.instantiate mi args) :: ds => some ([], mi, args, ds)
  | d :: ds => (firstCore? ds).map fun q => (d :: q.1, q.2.1, q.2.2.1, q.2.2.2)

/-- **The split fragment of a core module**: no tags, memories, tables, data or element
segments. -/
def splitMod (m : Silmaril.Wasm.Module) : Bool :=
  m.tags.isEmpty && m.memories.isEmpty && m.tables.isEmpty && m.data.isEmpty && m.elems.isEmpty

/-- The first-core fragment, as a Boolean (kernel-checkable). -/
def firstCoreFrag (r : RefComponent) : Bool :=
  match firstCore? r with
  | none => false
  | some (pre, mi, _, _) =>
    preOk 0 0 pre &&
      match (coreMods pre)[mi]? with
      | some m => m.imports.isEmpty && splitMod m
      | none => false

/-- **The first-core fragment**: the definitions before the first core instantiation are of the
forms `preOk` allows, and the module it instantiates has no imports and is in the split
fragment. -/
def FirstCoreFrag (r : RefComponent) : Prop := firstCoreFrag r = true

instance (r : RefComponent) : Decidable (FirstCoreFrag r) :=
  inferInstanceAs (Decidable (firstCoreFrag r = true))

end Silmaril.Wasm.Component.DecoderBridge
