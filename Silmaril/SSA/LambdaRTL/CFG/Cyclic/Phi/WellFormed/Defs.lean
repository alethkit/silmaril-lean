module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Defs

/-! # Global SSA well-formedness for normalized φ graphs

The certificate supplies names available on arrival at named blocks, before
their φ definitions. Each syntactic edge checks the successor's claims and
reads its selected φ operands at the end of that particular predecessor
route. Both arms of a case are checked, with their respective payload binders.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA

universe v w
variable {V K : Type w} {F : Type v}

/-- One occurrence of a definition, including case binders in either arm.
Count common prefixes only once. -/
def termDefinitions : Term V (Option K) F → List V
  | .br _ _ => []
  | .case _ x left y right => (x :: termDefinitions left) ++ (y :: termDefinitions right)

def bodyDefinitions : Body V (Option K) F → List V
  | .let1 x _ next => x :: bodyDefinitions next
  | .let2 x y _ next => x :: y :: bodyDefinitions next
  | .term tail => termDefinitions tail

/-- Every static definition in the table, including the declared entry inputs. -/
def definitions (graph : Graph V K F) (inputs : List V) : List V :=
  inputs ++ bodyDefinitions graph.entry ++
    graph.blocks.flatMap (fun (_, block) => block.rows.map Row.dst ++ bodyDefinitions block.body)

inductive Access (V : Type w) where
  | read (names : List V)
  | define (names : List V)

/-- A path through one body and one chosen terminator leaf. An absent target returns. -/
structure Route (V K : Type w) where
  target : Option K
  accesses : List (Access V)

def Access.definitions : List (Access V) → List V
  | [] => []
  | .read _ :: rest => definitions rest
  | .define names :: rest => names ++ definitions rest

/-- Every leaf gives one syntactic route. Internal branches read the selected
φ column. The internal jump's unused nominal payload contributes no reads. -/
def termRoutes (edgeReads : K → List V) : Term V (Option K) F → List (Route V K)
  | .br none value => [⟨none, [.read value.fvList]⟩]
  | .br (some target) _ => [⟨some target, [.read (edgeReads target)]⟩]
  | .case operand x left y right =>
      (termRoutes edgeReads left).map (fun route =>
        { route with accesses := .read operand.fvList :: .define [x] :: route.accesses }) ++
      (termRoutes edgeReads right).map (fun route =>
        { route with accesses := .read operand.fvList :: .define [y] :: route.accesses })

def bodyRoutes (edgeReads : K → List V) : Body V (Option K) F → List (Route V K)
  | .let1 x operand next => (bodyRoutes edgeReads next).map fun route =>
      { route with accesses := .read operand.fvList :: .define [x] :: route.accesses }
  | .let2 x y operand next => (bodyRoutes edgeReads next).map fun route =>
      { route with accesses := .read operand.fvList :: .define [x, y] :: route.accesses }
  | .term tail => termRoutes edgeReads tail

variable [DecidableEq K]

/-- The φ operands read at a predecessor's terminator on the edge to the target. -/
def edgeReads (graph : Graph V K F) (source : Option K) (target : K) : List V :=
  (graph.blocks.lookup target).elim [] fun block => (arguments source block.rows).flatMap Val.fvList

/-- A named block defines all its φ destinations before any body instruction. -/
def routes (graph : Graph V K F) (source : Option K) : List (Route V K) :=
  match source with
  | none => bodyRoutes (edgeReads graph none) graph.entry
  | some label => (graph.blocks.lookup label).elim [] fun block =>
      (bodyRoutes (edgeReads graph source) block.body).map fun route =>
        { route with accesses := .define (block.rows.map Row.dst) :: route.accesses }

/-- A structural path from the entry to the start of a block, with its prior
accesses in execution order. A return has no successor block. -/
inductive EntryPath (graph : Graph V K F) : Option K → List (Access V) → Prop where
  | entry : EntryPath graph none []
  | follow {source : Option K} {past : List (Access V)} {route : Route V K} {target : K}
      (path : EntryPath graph source past) (chosen : route ∈ routes graph source)
      (edge : route.target = some target) : EntryPath graph (some target) (past ++ route.accesses)

/-- The unique definition of each read name is available before that read on
every structural entry path reaching it, or the name is a declared input. -/
structure WellFormed [DecidableEq V] (graph : Graph V K F) (inputs : List V) : Prop where
  normalized : graph.check = true
  unique : (definitions graph inputs).Nodup
  available : ∀ {source past route}, EntryPath graph source past → route ∈ routes graph source →
    ∀ {before names after}, past ++ route.accesses = before ++ .read names :: after →
      names ⊆ inputs ++ Access.definitions before

/-- Finite arrival claims for named blocks. All targets of checked routes must
have a row. Blocks outside the certificate need no arrival claim. -/
abbrev Certificate (V K : Type w) := List (K × List V)

def arrival (inputs : List V) (certificate : Certificate V K) : Option K → Option (List V)
  | none => some inputs
  | some label => certificate.lookup label

variable [DecidableEq V]

/-- Scan in execution order, failing at the first read outside the available set. -/
def Access.scan (available : List V) : List (Access V) → Option (List V)
  | [] => some available
  | .read names :: rest =>
      if names.all (fun name => available.contains name) then scan available rest else none
  | .define names :: rest => scan (available ++ names) rest

def checkRoute (certificate : Certificate V K) (available : List V) (route : Route V K) : Bool :=
  (Access.scan available route.accesses).any fun seen =>
    route.target.elim true fun target =>
      (certificate.lookup target).any fun required => required.all (fun name => seen.contains name)

/-- Validate a closed set of arrival claims starting at the entry and check
global static uniqueness. Extra certified blocks are checked as well. -/
def check (graph : Graph V K F) (inputs : List V) (certificate : Certificate V K) : Bool :=
  graph.check && (decide (definitions graph inputs).Nodup &&
    (decide (certificate.map Prod.fst).Nodup &&
      ((routes graph none).all (checkRoute certificate inputs) &&
        certificate.all fun (label, required) =>
          (graph.blocks.lookup label).isSome &&
            (routes graph (some label)).all (checkRoute certificate required))))

/-- Optional global SSA admission before the existing shape-checked lowering. -/
def compile (graph : Graph V K F) (inputs : List V) (certificate : Certificate V K) :
    Option (CFG (Option V × Nat) (Option K) F) :=
  if check graph inputs certificate then Phi.compile graph else none

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA
