module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite

open Assignment (LexicalBlock)
open Functions
open Lists (Outcome State)
open Lists.Iteration (Flow)

local notation "Expr" => Lowering.Resolve.SourceExpr

/-- The checked continuation copies the just-defined name and uses that
copy as the callee of an assignment. No intervening statement may change it. -/
structure Assignment (block : LexicalBlock) where
  copy : String
  copyOwned : copy ∈ block.owned
  copyLegal : copy.toList.head? ≠ some '$'
  destination : String
  destinationOwned : destination ∈ block.owned
  arguments : List Expr
  codes : List Lowering.Expr
  argumentReads : List Binding
  operands : Call.Arguments block arguments codes argumentReads

@[expose] def Assignment.source {block : LexicalBlock} (call : Assignment block)
    (defined : String) (rest : Statement) : Statement :=
  .seq (.assign call.copy (.scalar (.read defined)))
    (.seq (.assign call.destination (.call (.scalar (.read call.copy)) call.arguments [] none none)) rest)

@[expose] def Assignment.code {block : LexicalBlock} (call : Assignment block)
    (defined : String) (tail : Functions.Body) : Functions.Body :=
  .seq (.assignExpr (fileSlot call.copy) (Leaf.readOperand (fileSlot defined)))
    (.seq (.assignExpr (fileSlot call.destination) (Call.expression call.copy call.codes)) tail)

@[expose] def Assignment.reads {block : LexicalBlock} (call : Assignment block) (defined : String) : List Binding :=
  fileSlot defined :: fileSlot call.copy :: call.argumentReads

/-- A suite interleaves lexical assignments, local definitions and calls
to just-defined children. Invoked children use the existing recursive
suite without call statements. The last index lists the call IDs that
must be available in this activation. -/
inductive Elaborates :
    LexicalBlock → Statement → Program → ResolvedBody → Program → Emissions → List DeclarationId → Prop where
  | plain {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody} {emitted : Emissions} :
      Recursive.Elaborates block source seed resolved final emitted → Elaborates block source seed resolved final emitted []
  | assignments {block : LexicalBlock} {leading : List (String × Expr)} {code : List (String × Lowering.Expr)} {reads : List Binding}
      {rest : Statement} {seed final : Program} {tail : ResolvedBody} {emitted : Emissions} {calls : List DeclarationId} :
      Body.ElaboratesPrefix block leading code reads → Elaborates block rest seed tail final emitted calls →
      Elaborates block (Body.prependSource leading rest) seed
        ⟨Body.prependCode code tail.code, reads ++ tail.reads⟩ final emitted calls
  | define {block : LexicalBlock} {rest : Statement} {seed childTable final : Program} {tail : ResolvedBody}
      {descendants later : Emissions} {calls childCalls : List DeclarationId} (site : Site block) :
      Elaborates site.block site.source seed site.body childTable descendants childCalls →
      Elaborates block rest (childTable.push site.declaration) tail final later calls →
      Elaborates block (.seq site.statement rest) seed
        ⟨.seq (.define (fileSlot site.name) childTable.size) tail.code, site.reads ++ tail.reads⟩ final
        (descendants ++ (childTable.size, site.declaration) :: later) calls
  | call {block : LexicalBlock} {rest : Statement} {seed childTable final : Program} {tail : ResolvedBody}
      {descendants later : Emissions} {calls : List DeclarationId} (site : Site block)
      (legal : site.name.toList.head? ≠ some '$') (assignment : Assignment block) :
      Recursive.Elaborates site.block site.source seed site.body childTable descendants →
      Elaborates block rest (childTable.push site.declaration) tail final later calls →
      Elaborates block (.seq site.statement (assignment.source site.name rest)) seed
        ⟨.seq (.define (fileSlot site.name) childTable.size) (assignment.code site.name tail.code),
          site.reads ++ (assignment.reads site.name ++ tail.reads)⟩ final
        (descendants ++ (childTable.size, site.declaration) :: later) (childTable.size :: calls)

/-- The continuation of each stage runs only if that stage succeeds.
After a successful call, the destination receives the return value in
the restored caller frame before the rest of the suite runs. -/
inductive Runs (block : LexicalBlock) : State → Statement → Functions.Body → Outcome Flow → Prop where
  | plain {state : State} {source : Statement} {code : Functions.Body} {out : Outcome Flow} :
      Sequence.Runs block state source code out → Runs block state source code out
  | assignments {state : State} {leading : List (String × Expr)} {code : List (String × Lowering.Expr)}
      {rest : Statement} {tail : Functions.Body} {result : Outcome Unit} {out : Outcome Flow} :
      Body.RunsPrefix block state leading code result →
      (∀ entered, result = .ok () entered → Runs block entered rest tail out) →
      Runs block state (Body.prependSource leading rest) (Body.prependCode code tail) (result.resume fun _ _ => out)
  | define {state : State} {rest : Statement} {tail : Functions.Body} {id : DeclarationId}
      {site : Site block} {captures : List Lists.Capture} {result out : Outcome Flow} :
      Installs state site.free captures →
      Nested.SiteResult block site.name site.parameters site.defaults id captures state result →
      (∀ installed, result = .ok .next installed → Runs block installed rest tail out) →
      Runs block state (.seq site.statement rest) (.seq (.define (fileSlot site.name) id) tail)
        (result.resume fun _ _ => out)
  | call {state : State} {rest : Statement} {tail : Functions.Body} {id : DeclarationId}
      {site : Site block} {assignment : Assignment block} {address : Nat}
      {result : Outcome Lists.Value} {out : Outcome Flow} :
      Body.Evaluates block state (.scalar (.read site.name)) (Leaf.readOperand (fileSlot site.name))
        (.ok (.function address) state) →
      Call.Runs site block id assignment.copy assignment.arguments assignment.codes
        (state.write (fileSlot assignment.copy) (.function address)) result →
      (∀ value returned, result = .ok value returned →
        Runs block (returned.write (fileSlot assignment.destination) value) rest tail out) →
      Runs block state (assignment.source site.name rest) (assignment.code site.name tail)
        (result.resume fun _ _ => out)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite
