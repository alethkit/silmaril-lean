module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Thms

/-! # Generating the checked admission of a split φ graph -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)

universe u v
variable {V W K J Base : Type u} {F : Type v} {n : Nat}
variable (plan : Plan V W K J)

/-- Extend the renamed capture list at the older end so that all original
positions and types are preserved. New slots are read from the renamed store. -/
def extendedNames (names : Fin n → Option V) (extra : List (Option W × Ty Base)) :
    Fin (n + extra.length) → Option W :=
  Fin.addCases (fun i => (names i).map plan.register) (fun i => extra[i].1)

def extendedTypes (β : BoundCtx (Ty Base) n) (extra : List (Option W × Ty Base)) :
    BoundCtx (Ty Base) (n + extra.length) :=
  .ofFin (Fin.addCases β.get fun i => extra[i].2)

variable [DecidableEq V] [DecidableEq K] [DecidableEq W] [DecidableEq J]
  [HasTy F (Ty Base)]

/-- Carry over the old arrival claims. A forwarding block whose destination
has a claim needs that claim and exactly the old φ reads on the selected edge.
Omit the forwarding claim when the destination was outside the certificate. -/
def splitCertificate (source : Phi.Graph V K F) (certificate : Phi.GlobalSSA.Certificate V K) :
    Phi.GlobalSSA.Certificate W J :=
  let renamed := certificate.map fun (key, names) => (plan.label key, names.map plan.register)
  match certificate.lookup plan.header with
  | none => renamed
  | some required =>
    (plan.forward,
      (required ++ Phi.GlobalSSA.edgeReads source plan.predecessor plan.header).map plan.register) :: renamed

/-- The generated profile and the actual checked, purely closed split graph.
The new slots and block types are outputs of synthesis. -/
structure Generated (source : Phi.Graph V K F) (inputs : List V)
    (names : Fin n → Option V) (β : BoundCtx (Ty Base) n) (exits : Fin 1 → Ty Base) where
  extra : List (Option W × Ty Base)
  blocks : Fin (blockCount (plan.rewrite source)) → Ty Base
  checked : Checked plan source (plan.rewrite source)
  admitted : Certified.Admission (plan.rewrite source) (inputs.map plan.register)
    (extendedNames plan names extra) (extendedTypes β extra) blocks exits
  closed : Closed admitted

/-- Associate the cells of a right-nested packet type with its names. -/
def packetTypes {A : Type u} : List A → Ty Base → Option (List (A × Ty Base))
  | [], _ => some []
  | name :: names, .product ty tail => (packetTypes names tail).map ((name, ty) :: ·)
  | _, _ => none

/-- Recover the types read by a φ operand from its checked packet-cell type. -/
def operandTypes : Val V → Ty Base → Option (List (V × Ty Base))
  | .var name, ty => some [(name, ty)]
  | .unit, .unit => some []
  | .pair left right, .product a b => do
    let leftTypes ← operandTypes left a
    let rightTypes ← operandTypes right b
    return leftTypes ++ rightTypes
  | _, _ => none

def packetProfile (support : List V) (newSupport : List W)
    (added : List (V × Ty Base)) (old : Ty Base) : Option (Ty Base) := do
  let .product payload tuple := old | none
  let registerTypes ← packetTypes support tuple
  let newTypes ← newSupport.mapM fun name => (registerTypes ++ added).lookup (plan.register.symm name)
  return .product payload (newTypes.foldr .product .unit)

/-- Build the candidate profiles in the actual versioner's register and block
orders. Keep each old block's φ payload type. The forwarding block has a
unit payload and uses the old destination's register types, extended with
types recovered from the selected φ column. -/
def splitProfiles (source : Phi.Graph V K F)
    (names : Fin n → Option V) (blocks : Fin (blockCount source) → Ty Base) :
    Option (List (Option W × Ty Base) × (Fin (blockCount (plan.rewrite source)) → Ty Base)) := do
  let lowered := Phi.lower source
  let target := Phi.lower (plan.rewrite source)
  let lexical := Versioning.compile lowered
  let splitLexical := Versioning.compile target
  let oldSupport := (Versioning.registers lowered).filterMap id
  let newSupport := (Versioning.registers target).filterMap id
  let oldBlocks := (List.finRange lexical.blocks.length).map fun i => (lexical.blocks[i].1, blocks i)
  let .product headerPayload headerTuple ← oldBlocks.lookup (some plan.header) | none
  let rows ← (source.blocks.lookup plan.header).map Phi.Block.rows
  let cells ← packetTypes (Phi.arguments plan.predecessor rows) headerPayload
  let movedTypes ← cells.mapM fun (operand, ty) => operandTypes operand ty
  let added := movedTypes.flatten
  let oldRegisterTypes ← packetTypes oldSupport headerTuple
  let allTypes := oldRegisterTypes ++ added
  let oldNames := (List.finRange n).map fun i => (names i).map plan.register
  let needed := (splitLexical.entry.toRegion.fvList.filterMap fun (name, version) =>
    if version = 0 ∧ name ∉ oldNames then some name else none).dedup
  let extra ← needed.mapM fun name => do
    let ty ← name.elim (some .unit) (fun reg => allTypes.lookup (plan.register.symm reg))
    return (name, ty)
  let renamedBlocks := oldBlocks.map fun (label, ty) => (label.map plan.label, ty)
  let profiles ← NamedFlat.tabulate splitLexical.blocks.length fun i => do
    let label := splitLexical.blocks[i].1
    let old ← if label = some plan.forward then some (.product .unit headerTuple)
      else renamedBlocks.lookup label
    packetProfile plan oldSupport newSupport added old
  return (extra, profiles)

/-- Reuse the original admission and its finite arrival certificate. Generate
the split profile and recheck target normalization, global SSA, exact typing,
and pure closure. The caller supplies no target typing or arrival claims. -/
def generate [DecidableEq Base] {source : Phi.Graph V K F} {inputs : List V}
    {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}
    {blocks : Fin (blockCount source) → Ty Base} {exits : Fin 1 → Ty Base}
    (original : Certified.Admission source inputs names β blocks exits)
    (certificate : Phi.GlobalSSA.Certificate V K) : Option (Generated plan source inputs names β exits) :=
  let target := plan.rewrite source
  if edge : plan.hasEdge source = true then
    match splitProfiles plan source names blocks with
    | none => none
    | some (extra, profiles) =>
      match Certified.admit target (inputs.map plan.register) (splitCertificate plan source certificate)
          (extendedNames plan names extra) (extendedTypes β extra) profiles exits with
      | none => none
      | some admitted =>
        (PureCapture.close admitted).map fun closed =>
          let checked : Checked plan source target :=
            ⟨original.wellFormed.normalized, edge, admitted.wellFormed.normalized, rfl⟩
          ⟨extra, profiles, checked, admitted, closed⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
