module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Defs

/-! Ordered admission over the exact results of a typed module link. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial (Primitives)
open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {imports importsL importsR exports : Ports (Ty V S)}
variable {past pastL pastR sigs sigsL sigsR : List (Ports (Ty V S))}

/-- Align the actual bindings in two modules in link order. The plan
chooses the single paired φ seed, the paired λ extensions, and which
bindings to link without admitting their callable outputs. The types
enforce a common signature at each λ pair. -/
inductive Plan (Op : Dialect.{u, v} (ValueSort V S) S) (importsL importsR exports : Ports (Ty V S)) :
    Bool → {pastL sigsL pastR sigsR : List (Ports (Ty V S))} →
    ModuleTerm Op importsL pastL sigsL exports → ModuleTerm Op importsR pastR sigsR exports → Type (max u v + 1) where
  | done {pastL pastR : List (Ports (Ty V S))} {left : Wires importsL pastL exports} {right : Wires importsR pastR exports} :
      Plan Op importsL importsR exports true (.ret left) (.ret right)
  | skipL {seeded : Bool} {pastL sigsL pastR sigsR : List (Ports (Ty V S))}
      {head : Ports (Ty V S)} {node : VertexTerm Op importsL pastL head}
      {rest : ModuleTerm Op importsL (pastL ++ [head]) sigsL exports} {right : ModuleTerm Op importsR pastR sigsR exports}
      (next : Plan Op importsL importsR exports seeded rest right) :
      Plan Op importsL importsR exports seeded (.bind node rest) right
  | skipR {seeded : Bool} {pastL sigsL pastR sigsR : List (Ports (Ty V S))}
      {head : Ports (Ty V S)} {node : VertexTerm Op importsR pastR head}
      {left : ModuleTerm Op importsL pastL sigsL exports} {rest : ModuleTerm Op importsR (pastR ++ [head]) sigsR exports}
      (next : Plan Op importsL importsR exports seeded left rest) :
      Plan Op importsL importsR exports seeded left (.bind node rest)
  | seed {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {membersL membersR : List (Function V S)}
      {left : PhiTerm Op importsL pastL membersL} {right : PhiTerm Op importsR pastR membersR}
      {restL : ModuleTerm Op importsL (pastL ++ [memberPorts membersL]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [memberPorts membersR]) sigsR exports}
      (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports false (.bind (.phi left) restL) (.bind (.phi right) restR)
  | lambda {pastL sigsL pastR sigsR : List (Ports (Ty V S))} {fn : Function V S}
      {left : LambdaTerm Op importsL pastL fn} {right : LambdaTerm Op importsR pastR fn}
      {restL : ModuleTerm Op importsL (pastL ++ [[fn.port]]) sigsL exports}
      {restR : ModuleTerm Op importsR (pastR ++ [[fn.port]]) sigsR exports}
      (next : Plan Op importsL importsR exports true restL restR) :
      Plan Op importsL importsR exports true (.bind (.lambda left) restL) (.bind (.lambda right) restR)

abbrev Row (family : Family m) {ports : Ports (Ty V S)} (values : Tuple m.Val ports) :=
  ∀ {port : Ty V S} (p : Port ports port), Option (PLift (family (values.get p)))

/-- The proof table is indexed by the linker locals it describes. Every
cell refers to the value at that exact typed output position. -/
def Table (family : Family m) : {past : List (Ports (Ty V S))} → Locals m.Val past → Type u
  | [], _ => PUnit
  | _ :: _, locals => Row family locals.1 × Table family locals.2

def Table.empty (family : Family m) : {past : List (Ports (Ty V S))} → (locals : Locals m.Val past) → Table family locals
  | [], _ => PUnit.unit
  | _ :: _, locals => ⟨fun _ => none, Table.empty family locals.2⟩

def Table.get {family : Family m} : {past : List (Ports (Ty V S))} → {locals : Locals m.Val past} →
    Table family locals → (i : Fin past.length) → Row family (locals.get i)
  | [], _, _, i => i.elim0
  | head :: tail, locals, table, i => fun p =>
    (Fin.cases (motive := fun (j : Fin (head :: tail).length) => Row family (locals.get j))
      (fun {_t} p => table.1 p) (fun j {_t} p => Table.get table.2 j p) i) p

def Table.snoc {family : Family m} {ports : Ports (Ty V S)} {values : Tuple m.Val ports}
    (row : Row family values) : {past : List (Ports (Ty V S))} → {locals : Locals m.Val past} →
    Table family locals → Table family (locals.snoc values)
  | [], _, _ => ⟨row, PUnit.unit⟩
  | _ :: _, _, table => ⟨table.1, Table.snoc row table.2⟩

def Table.lift {family target : Family m}
    (includeValue : ∀ {port : Ty V S} {value : m.Val port}, family value → target value) :
    {past : List (Ports (Ty V S))} → {locals : Locals m.Val past} → Table family locals → Table target locals
  | [], _, _ => PUnit.unit
  | _ :: _, _, table => ⟨fun p => (table.1 p).map (fun cert => ⟨includeValue cert.down⟩), Table.lift includeValue table.2⟩

/-- Ordinary values are admitted at use. A nonordinary import has no
entry, while a callable output must have been admitted at its binding. -/
def Table.available {family : Family m} {entry : Tuple m.Val imports} {locals : Locals m.Val past}
    (table : Table family locals)
    (ordinary : ∀ {port : Ty V S} (value : m.Val port), ordinaryPort port = true → family value) :
    Available family entry locals :=
  fun {port} origin =>
    if plain : ordinaryPort port = true then some ⟨ordinary _ plain⟩
    else match origin with
      | .arg _ => none
      | .output row p => table.get row p

def memberRow {family : Family m} :
    (members : List (Function V S)) → (values : (i : Fin members.length) → m.Val members[i].port) →
    (∀ i, family (values i)) → Row family (memberValues members values)
  | [], _, _, _, p => nomatch p
  | _ :: _, _, known, _, .head => some ⟨known 0⟩
  | _ :: rest, values, known, _, .tail p => memberRow rest (fun i => values i.succ) (fun i => known i.succ) p

def exportWire {family : Family m} {entry : Tuple m.Val imports} {locals : Locals m.Val past}
    (available : Available family entry locals) :
    {ports : Ports (Ty V S)} → (wires : Wires imports past ports) → {port : Ty V S} →
    (p : Port ports port) → Option (PLift (family ((wires.read entry locals).get p)))
  | [], .nil, _, p => nomatch p
  | _ :: _, .cons origin _, _, .head => available origin
  | _ :: _, .cons _ rest, _, .tail p => exportWire available rest p

variable {primitives : Primitives m σ} {ids : GlobalRel}

structure Checked (primitives : Primitives m σ) (ids : GlobalRel)
    (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR) where
  familyL : Family m
  familyR : Family m
  keys : LambdaKeys V S
  certified : LinkedFamily primitives ids familyL familyR keys
  left : Table familyL localsL
  right : Table familyR localsR

inductive State (primitives : Primitives m σ) (ids : GlobalRel)
    (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR) : Bool → Type (max u v w) where
  | unseeded : State primitives ids localsL localsR false
  | seeded (checked : Checked primitives ids localsL localsR) : State primitives ids localsL localsR true

def State.skipL {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR} {ports : Ports (Ty V S)}
    (values : Tuple m.Val ports) :
    {seeded : Bool} → State primitives ids localsL localsR seeded → State primitives ids (localsL.snoc values) localsR seeded
  | _, .unseeded => .unseeded
  | _, .seeded checked =>
    .seeded ⟨checked.familyL, checked.familyR, checked.keys, checked.certified, checked.left.snoc (fun _ => none), checked.right⟩

def State.skipR {localsL : Locals m.Val pastL} {localsR : Locals m.Val pastR} {ports : Ports (Ty V S)}
    (values : Tuple m.Val ports) :
    {seeded : Bool} → State primitives ids localsL localsR seeded → State primitives ids localsL (localsR.snoc values) seeded
  | _, .unseeded => .unseeded
  | _, .seeded checked =>
    .seeded ⟨checked.familyL, checked.familyR, checked.keys, checked.certified, checked.left, checked.right.snoc (fun _ => none)⟩

/-- The certificate is indexed by the ordinary executable link outcomes.
A successful certificate consumes the exact exported values at the selected
port, independently of how the paired link relation was obtained. -/
def AdmittedExport (primitives : Primitives m σ) (ids : GlobalRel) {fn : Function V S}
    (port : Port exports fn.port) : Outcome m σ exports → Outcome m σ exports → Prop
  | .linked left _, .linked right _ => ExportAdmission primitives ids (left.get port) (right.get port)
  | _, _ => False

abbrev linkTerm (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past)
    (term : ModuleTerm Op imports past sigs exports) (store : σ) : Outcome m σ exports :=
  Executable.linkTable actions unitId inputs past sigs locals term.vertices term.results store

theorem linkTerm_bind (actions : Actions m σ) (unitId : Nat)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val past) {ports : Ports (Ty V S)}
    (definition : VertexTerm Op imports past ports)
    (rest : ModuleTerm Op imports (past ++ [ports]) sigs exports) (store : σ) :
    linkTerm actions unitId inputs locals (.bind definition rest) store =
      match Executable.linkVertex actions unitId inputs locals definition.toGraph store with
      | .linked values middle => linkTerm actions unitId inputs (locals.snoc values) rest middle
      | .undefined failure => .undefined failure := by
  unfold linkTerm
  rw [Executable.linkTable, show (ModuleTerm.bind definition rest).vertices 0 = definition.toGraph from Fin.cases_zero,
    show (fun i : Fin sigs.length => (ModuleTerm.bind definition rest).vertices i.succ) = rest.vertices from
      funext fun i => Fin.cases_succ i]
  simp only [ModuleTerm.results, site, Fin.cases_zero]
  cases Executable.linkVertex actions unitId inputs locals definition.toGraph store <;> rfl

variable [DecidableEq (Ty V S)]

/-- Walk each module in its own link order. Skipped rows still run the
actual linker, including any partial δ initialization. The selected φ/λ
rows use the exact values of the linker's non-effectful binding rules. -/
def walk (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (actions : Actions m σ)
    (ids : GlobalRel) (ordinary : OrdinaryOutputs Op) (unitL unitR : Nat)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    {fn : Function V S} (port : Port exports fn.port) :
    {seeded : Bool} → {pastL sigsL pastR sigsR : List (Ports (Ty V S))} →
    {left : ModuleTerm Op importsL pastL sigsL exports} → {right : ModuleTerm Op importsR pastR sigsR exports} →
    (localsL : Locals m.Val pastL) → (localsR : Locals m.Val pastR) → (storeL storeR : σ) →
    Plan Op importsL importsR exports seeded left right →
    State actions.toPrimitives ids localsL localsR seeded →
    Option (PLift (AdmittedExport actions.toPrimitives ids port
      (linkTerm actions unitL inputsL localsL left storeL) (linkTerm actions unitR inputsR localsR right storeR)))
  | _, _, _, _, _, _, _, _, _, _, _, .done (left := outputsL) (right := outputsR), .seeded checked => do
    let selectedL ← exportWire (checked.left.available checked.certified.ordinaryL) outputsL port
    let selectedR ← exportWire (checked.right.available checked.certified.ordinaryR) outputsR port
    pure ⟨checked.certified.forExports selectedL.down selectedR.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR, .skipL (node := node) next, state =>
    match ran : Executable.linkVertex actions unitL inputsL localsL node.toGraph storeL with
    | .undefined _ => none
    | .linked values middle => do
      let checked ← walk keys actions ids ordinary unitL unitR inputsL inputsR port
        (localsL.snoc values) localsR middle storeR next (state.skipL values)
      pure ⟨by rw [linkTerm_bind, ran]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR, .skipR (node := node) next, state =>
    match ran : Executable.linkVertex actions unitR inputsR localsR node.toGraph storeR with
    | .undefined _ => none
    | .linked values middle => do
      let checked ← walk keys actions ids ordinary unitL unitR inputsL inputsR port
        localsL (localsR.snoc values) storeL middle next (state.skipR values)
      pure ⟨by rw [linkTerm_bind, ran]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .seed (membersL := membersL) (membersR := membersR) (left := left) (right := right) next, .unseeded => do
    let groupL : Group m membersL := ⟨_, left.captures.read inputsL localsL, left.toGraph.definitions⟩
    let groupR : Group m membersR := ⟨_, right.captures.read inputsR localsR, right.toGraph.definitions⟩
    let seed ← LinkedFamily.ofGroups keys actions.toPrimitives ids ordinary groupL groupR
    let leftTable := (Table.empty groupL.In localsL).snoc (memberRow membersL groupL.ref (fun slot => .member slot))
    let rightTable := (Table.empty groupR.In localsR).snoc (memberRow membersR groupR.ref (fun slot => .member slot))
    let checked ← walk keys actions ids ordinary unitL unitR inputsL inputsR port
      (localsL.snoc (memberValues membersL groupL.ref)) (localsR.snoc (memberValues membersR groupR.ref))
      storeL storeR next (.seeded ⟨groupL.In, groupR.In, ⟨[], []⟩, seed.down, leftTable, rightTable⟩)
    pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩
  | _, _, _, _, _, _, _, localsL, localsR, storeL, storeR,
      .lambda (left := left) (right := right) next, .seeded earlier => do
    let certified ← earlier.certified.addLambda keys ordinary
      (earlier.left.available earlier.certified.ordinaryL) (earlier.right.available earlier.certified.ordinaryR)
      left.toGraph right.toGraph
    let calleeL := linkedLambda left.toGraph inputsL localsL
    let calleeR := linkedLambda right.toGraph inputsR localsR
    let familyL : Family m := WithExport earlier.familyL calleeL
    let familyR : Family m := WithExport earlier.familyR calleeR
    let rowL : Row familyL (.cons calleeL .nil) := fun p => match p with
      | .head => some ⟨.exported⟩
      | .tail p => nomatch p
    let rowR : Row familyR (.cons calleeR .nil) := fun p => match p with
      | .head => some ⟨.exported⟩
      | .tail p => nomatch p
    let tableL := (earlier.left.lift (fun known => WithExport.inherited known)).snoc rowL
    let tableR := (earlier.right.lift (fun known => WithExport.inherited known)).snoc rowR
    let checked ← walk keys actions ids ordinary unitL unitR inputsL inputsR port
      (localsL.snoc (.cons calleeL .nil)) (localsR.snoc (.cons calleeR .nil)) storeL storeR next
      (.seeded ⟨familyL, familyR, _, certified.down, tableL, tableR⟩)
    pure ⟨by simp only [linkTerm_bind, VertexTerm.toGraph, Executable.linkVertex]; exact checked.down⟩

/-- Check an ordered pair of complete link prefixes, then read the
selected export from the generated membership tables. The plan contains
only binding selections. Each λ step checks separation using signatures,
ordered capture types and outer body vertex counts. Related successful link outcomes
and primitive compatibility remain premises for paired invocation. -/
def admit (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key] (actions : Actions m σ)
    (ids : GlobalRel) (ordinary : OrdinaryOutputs Op) (unitL unitR : Nat)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    (left : OmegaTerm Op importsL exports sigsL) (right : OmegaTerm Op importsR exports sigsR)
    (plan : Plan Op importsL importsR exports false left.region right.region)
    {fn : Function V S} (port : Port exports fn.port) (storeL storeR : σ) :
    Option (PLift (AdmittedExport actions.toPrimitives ids port
      (Executable.link actions unitL left.toGraph inputsL storeL)
      (Executable.link actions unitR right.toGraph inputsR storeR))) :=
  walk keys actions ids ordinary unitL unitR inputsL inputsR port (pastL := []) (pastR := [])
    (left := left.region) (right := right.region) PUnit.unit PUnit.unit storeL storeR plan .unseeded

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix
