module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

/-!
# Build a cyclic GVN view from an actual pure Loop Region

The native latch ports come first in tuple order, followed by the actual
header producers in table order. The builder decodes every ordered input
and observation by exact typed origin, checks the instantaneous producer
order, and constructs the existing activation certificate.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder

open Activation (HeaderWire Site View headerInput headerLatch inputSlot operandWires sourceWire)
open Diamond (Signature Ty ValueSort dataPorts)
open RVSDG (Origin Port Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out t : ValueSort Data}

abbrev EntryWire (inputs : List (ValueSort Data)) (entrySigs : List (List (Ty Data)))
    (t : ValueSort Data) := Origin (dataPorts inputs) (extend [] entrySigs) (.value t)

/-- A native location of a vertex in the view, before decoding its operands. -/
inductive Location (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) (t : ValueSort Data) where
  | phi (port : Port (dataPorts carried) (.value t))
  | pure (producer : Producer loop.header t)

variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}

def Location.origin : Location loop t → HeaderWire inputs carried headerSigs t
  | .phi port => .arg (headerLatch port (dataPorts inputs))
  | .pure producer => producer.origin

def locations (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    List (Σ sort, Location loop sort) :=
  ((Pass.operandPorts carried).map fun ⟨sort, port⟩ => ⟨sort, .phi port⟩) ++
    ((Pass.producers loop.header).map fun ⟨sort, producer⟩ => ⟨sort, .pure producer⟩)

abbrev Vertex (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :=
  Fin (locations loop).length

abbrev sorts (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) (i : Vertex loop) :
    ValueSort Data := ((locations loop).get i).1

abbrev location (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) (i : Vertex loop) :
    Location loop (sorts loop i) := ((locations loop).get i).2

/-- Native origins are determined before decoding any incoming edges. -/
def sourceOrigin (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    Source inputs (sorts loop) t → HeaderWire inputs carried headerSigs t
  | .argument port => .arg (headerInput (dataPorts carried) port)
  | .producer i same => same ▸ (location loop i).origin

abbrev Sites (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :=
  (i : Vertex loop) → Site loop (sorts loop) (sorts loop i)

abbrev Matches (sites : Sites loop) :=
  ∀ i, (sites i).origin = (location loop i).origin

theorem sourceWire_eq (sites : Sites loop) (matchesOrigins : Matches sites)
    (source : Source inputs (sorts loop) t) :
    sourceWire sites source = sourceOrigin loop source := by
  cases source with
  | argument => rfl
  | producer i same => exact congrArg (fun wire => same ▸ wire) (matchesOrigins i)

theorem origin_eq {T : Type u} {args : List T} {scope : List (List T)} {ty : T}
    (lhs rhs : Origin args scope ty) (same : lhs.address = rhs.address) : lhs = rhs :=
  congrArg (fun (wires : Wires args scope [ty]) => wires.get .head)
    (RVSDG.NestedTheta.Equality.addresses_injective (.cons lhs .nil) (.cons rhs .nil)
      (congrArg (fun address => [address]) same))

section Decode

variable [DecidableEq (ValueSort Data)]

/-- Enumerate fixed arguments of the requested sort in tuple order. -/
def argumentPorts (t : ValueSort Data) : (ctx : List (ValueSort Data)) → List (Port ctx t)
  | [] => []
  | sort :: rest =>
    let tail := (argumentPorts t rest).map Port.tail
    if same : sort = t then (same ▸ Port.head) :: tail else tail

/-- The admitted entry occurrence is a direct read of a fixed argument. -/
def decodeEntry? (wire : EntryWire inputs entrySigs t) :
    Option {port : Port inputs t // wire = .arg (inputSlot port)} :=
  (argumentPorts t inputs).findSome? fun port =>
    let candidate : EntryWire inputs entrySigs t := .arg (inputSlot port)
    if same : wire.address = candidate.address then some ⟨port, origin_eq wire candidate same⟩
    else none

/-- Recover the exact typed origin as either a fixed argument or a vertex. -/
def decodeHeader? (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (wire : HeaderWire inputs carried headerSigs t) :
    Option {source : Source inputs (sorts loop) t // sourceOrigin loop source = wire} :=
  let arguments := (argumentPorts t inputs).map Source.argument
  let vertices := (List.finRange (locations loop).length).filterMap fun i =>
    if same : sorts loop i = t then some (Source.producer i same) else none
  (arguments ++ vertices).findSome? fun source =>
    if same : (sourceOrigin loop source).address = wire.address then
      some ⟨source, origin_eq _ _ same⟩
    else none

abbrev CheckedOperands {ins : List (ValueSort Data)}
    (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (wires : Wires (Loop.headerPorts inputs carried) (extend [] headerSigs) (dataPorts ins)) :=
  {operands : Tuple (Source inputs (sorts loop)) ins //
    ∀ (sites : Sites loop), Matches sites → operandWires sites operands = wires}

def decodeOperands? (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    {ins : List (ValueSort Data)} →
      (wires : Wires (Loop.headerPorts inputs carried) (extend [] headerSigs) (dataPorts ins)) →
      Option (CheckedOperands loop wires)
  | [], .nil => some ⟨.nil, fun _ _ => rfl⟩
  | _ :: _, .cons head tail => do
    let decoded ← decodeHeader? loop head
    let rest ← decodeOperands? loop tail
    pure ⟨.cons decoded.1 rest.1, fun sites origins =>
      congrArg₂ Tuple.cons ((sourceWire_eq sites origins decoded.1).trans decoded.2) (rest.2 sites origins)⟩

abbrev CheckedSite (loc : Location loop t) :=
  {site : Site loop (sorts loop) t //
    site.origin = loc.origin ∧ ∀ (sites : Sites loop), Matches sites → site.Valid sites}

def decodeSite? (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (loc : Location loop t) : Option (CheckedSite loc) :=
  match loc with
  | .phi port =>
    (decodeEntry? ((loop.phiInputs .entry).get port)).bind fun entry =>
      (decodeHeader? loop ((loop.phiInputs .backedge).get port)).map fun feedback =>
        ⟨.phi entry.1 feedback.1 port, rfl, fun sites origins =>
          ⟨entry.2, ((sourceWire_eq sites origins feedback.1).trans feedback.2).symm⟩⟩
  | .pure producer =>
    let key := producer.key
    (decodeOperands? loop key.operands).map fun operands =>
      ⟨.pure key.opcode operands.1 producer, rfl, fun sites origins => by
        change producer.key = ⟨key.ins, key.opcode, operandWires sites operands.1⟩
        exact congrArg (GVN.Key.mk key.ins key.opcode) (operands.2 sites origins).symm⟩

end Decode

/-- Collect a finite dependent family only if every member is present. -/
def collectSites {k : Nat} {F : Fin k → Type w} :
    ((i : Fin k) → Option (F i)) → Option ((i : Fin k) → F i) := by
  induction k with
  | zero => exact fun _ => some (fun i => Fin.elim0 i)
  | succ k ih =>
    exact fun decoded => (decoded 0).bind fun head =>
      (ih (F := fun i => F i.succ) (fun i => decoded i.succ)).map fun tail => Fin.cases head tail

def Address.precedes {n : Nat} (consumer : Fin n) : Address (ValueSort Data) n → Bool
  | .argument .. => true
  | .producer _ source => decide (source < consumer)

def checkOrder (sites : Sites loop) : Bool :=
  (List.finRange (locations loop).length).all fun i =>
    if (sites i).node.isPure then (sites i).node.addresses.all (Address.precedes i) else true

theorem order_of_check (sites : Sites loop) (accepted : checkOrder sites = true)
    (i j : Vertex loop) (sort : ValueSort Data) (pureNode : (sites i).node.isPure = true)
    (operand : .producer sort j ∈ (sites i).node.addresses) : j < i := by
  have ordered := List.all_eq_true.mp accepted i (List.mem_finRange i)
  have edges : (sites i).node.addresses.all (Address.precedes i) = true := by
    simpa only [ite_eq_left pureNode] using ordered
  exact of_decide_eq_true (List.all_eq_true.mp edges _ operand)

structure Built (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) where
  graph : Cyclic.Graph Op inputs (sorts loop)
  view : View graph loop
  origins : Matches view.site

variable [DecidableEq (ValueSort Data)]

/-- Build the existing certificate for the direct-entry pure loop profile.
A failed origin check or instantaneous order check refuses the view. -/
def build? (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) : Option (Built loop) :=
  (collectSites fun i => decodeSite? loop (location loop i)).bind fun decoded =>
    let sites : Sites loop := fun i => (decoded i).1
    let origins : Matches sites := fun i => (decoded i).2.1
    if ordered : checkOrder sites = true then
      (decodeHeader? loop loop.predicate).bind fun guard =>
        (decodeHeader? loop loop.result).map fun result =>
          ⟨⟨fun i => (sites i).node, order_of_check sites ordered⟩,
           ⟨sites, fun _ => rfl, fun i => (decoded i).2.2 sites origins, guard.1, result.1,
             ((sourceWire_eq sites origins guard.1).trans guard.2).symm,
             ((sourceWire_eq sites origins result.1).trans result.2).symm⟩, origins⟩
    else none

variable [∀ ins out, DecidableEq (Op ins out)]

/-- Discover one shrinking step directly from a native loop. -/
def optimize? (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    Option (Deletion.DeletedLoop Op inputs carried entrySigs out) :=
  (build? loop).bind fun built => Pass.step? built.view

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder
