module

public import Silmaril.SSA.SeaOfNodes.Quads.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs

/-! # One cyclic ordered quad activation

The entry bank initializes the header ports. Each activation executes a
closed straight-line body, then reads the continuation predicate from its
updated bank. A taken backedge restarts with that whole bank.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop

open RVSDG (PortType Port Tuple Origin Wires Locals extend)
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open Silmaril.SSA.SeaOfNodes.Loop (Graph headerPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out test : ValueSort Data}
variable {args : List (Ty Data)} {past : List (List (Ty Data))}

/-- Execute the assignments and retain the entire final register bank. -/
def finalBank (m : Model.{u, v, w} Op) :
    Code Op regs test → Tuple (Val m.value) (dataPorts regs) → Tuple (Val m.value) (dataPorts regs)
  | .ret _, bank => bank
  | .assign dest op operands rest, bank =>
    finalBank m rest (write dest (m.run op (operands.map (fun _ src => bank.get src))) bank)

/-- The register selected by the straight-line terminator. -/
def returnPort : Code Op regs test → Port (dataPorts regs) (.value test)
  | .ret result => result
  | .assign _ _ _ rest => returnPort rest

/-- Numbered producers and the reaching origin of every outgoing register. -/
structure Transfer (Op : Signature.{u, v} Data) (regs : List (ValueSort Data))
    (args : List (Ty Data)) (past sigs : List (List (Ty Data))) where
  flow : Dataflow Op args past sigs
  outgoing : Wires args (extend past sigs) (dataPorts regs)

/-- Put a quad before a transfer whose wires see the newly appended result. -/
def Transfer.prepend {sigs : List (List (Ty Data))} (quad : Quad Op regs)
    (current : Wires args past (dataPorts regs))
    (tail : Transfer Op regs args (past ++ [[.value quad.result]]) sigs) :
    Transfer Op regs args past ([.value quad.result] :: sigs) :=
  ⟨.cons quad.op (quad.inputWires current) tail.flow, tail.outgoing⟩

/-- Both results are computed during the same traversal of the ordered block. -/
def compile : (code : Code Op regs test) → {past : List (List (Ty Data))} →
    Wires args past (dataPorts regs) → Transfer Op regs args past code.producers
  | .ret _, _, current => ⟨.nil, current⟩
  | .assign dest op operands rest, _, current =>
    (compile rest (rebind current dest)).prepend ⟨_, _, dest, op, operands⟩ current

/-- Address a carried port after the fixed entry arguments in the Loop header. -/
def carryPort {T : Type u} {ports : List T} {t : T} (port : Port ports t) :
    (input : List T) → Port (input ++ ports) t
  | [] => port
  | _ :: tail => .tail (carryPort port tail)

/-- Allocate every pending header definition as a typed argument before the
activation is translated. These ports will be fed by either incoming occurrence. -/
def headerVersions (regs : List (ValueSort Data)) :
    Wires (headerPorts regs regs) [] (dataPorts regs) :=
  tabulate _ (fun port => .arg (carryPort port (dataPorts regs)))

/-- The activation terminator reads the continuation register. A false
predicate exits with the specified register of that same updated bank. -/
structure Program (Op : Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) where
  activation : Code Op regs .predicate
  result : Port (dataPorts regs) (.value out)

def Program.step (p : Program Op regs out) (m : Model.{u,v,w} Op)
    (old : Tuple (Val m.value) (dataPorts regs)) :
    sortValue m.value out ⊕ Tuple (Val m.value) (dataPorts regs) :=
  let next := finalBank m p.activation old
  if (next.get (returnPort p.activation)).down then .inr next else .inl (next.get p.result)

/-- The empty preheader supplies the initialized bank. The backedge supplies
the final versions computed independently of the entry column. -/
def Program.lower (p : Program Op regs out) : Graph Op regs regs [] p.activation.producers out :=
  let lowered := compile p.activation (headerVersions regs)
  { preheader := .nil
    header := lowered.flow
    phiInputs
      | .entry => initial regs
      | .backedge => lowered.outgoing
    predicate := lowered.outgoing.get (returnPort p.activation)
    result := lowered.outgoing.get p.result }

/-- Count completed backedges. An exit from the first activation has count zero. -/
inductive Program.ReturnsAfter (p : Program Op regs out) (m : Model.{u,v,w} Op) :
    Nat → Tuple (Val m.value) (dataPorts regs) → sortValue m.value out → Prop where
  | exit {old result} (taken : p.step m old = .inl result) : ReturnsAfter p m 0 old result
  | backedge {count old next result} (taken : p.step m old = .inr next)
      (rest : ReturnsAfter p m count next result) : ReturnsAfter p m (count + 1) old result

def Program.Returns (p : Program Op regs out) (m : Model.{u,v,w} Op)
    (input : Tuple (Val m.value) (dataPorts regs)) (result : sortValue m.value out) : Prop :=
  ∃ count, p.ReturnsAfter m count input result

/-- Execute with a budget of completed backedges. Even budget zero permits an exit. -/
def Program.evalBackedges (p : Program Op regs out) (m : Model.{u,v,w} Op) :
    Nat → Tuple (Val m.value) (dataPorts regs) → Option (sortValue m.value out)
  | 0, old => match p.step m old with
    | .inl result => some result
    | .inr _ => none
  | budget + 1, old => match p.step m old with
    | .inl result => some result
    | .inr next => p.evalBackedges m budget next

end Silmaril.SSA.SeaOfNodes.Quads.Loop
