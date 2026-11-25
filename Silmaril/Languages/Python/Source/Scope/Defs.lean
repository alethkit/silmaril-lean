module

public import Silmaril.Languages.Python.Source.Syntax.Defs

/-! # Lexical scope of the Python module, function and class fragment

Collect declarations and binding occurrences in source order. Resolve names
using whole-block information, including assignments later in the block.
Child blocks retain both their directly used free names and any captures
they forward for descendants. Paths index child blocks in source order.
-/

namespace Silmaril.Languages.Python.Source

@[expose] public section

abbrev BlockPath := List Nat

inductive BlockKind where
  | module_
  | function
  | class_
  deriving BEq, DecidableEq, Repr

structure BlockContext where
  path : BlockPath
  kind : BlockKind
  parameters : List Name := []
  assigned : List Name := []
  read : List Name := []
  globals : List Name := []
  nonlocals : List Name := []
  deriving Repr

/-- A module, or an explicit global declaration in a function, ends the search. -/
def BlockContext.lookupBarrier (block : BlockContext) (name : Name) : Bool :=
  match block.kind with
  | .module_ => true
  | .function => block.globals.contains name
  | .class_ => false

/-- Closure binders of an enclosing block, including the synthetic class cell. -/
def BlockContext.binds (block : BlockContext) (name : Name) : Bool :=
  match block.kind with
  | .module_ => false
  | .function =>
    !block.globals.contains name && !block.nonlocals.contains name &&
      (block.parameters.contains name || block.assigned.contains name)
  | .class_ => name == "__class__"

/-- Search ancestors in order from the immediately enclosing block. -/
def enclosingBinding (name : Name) : List BlockContext → Option BlockPath
  | [] => none
  | block :: outer =>
    if block.lookupBarrier name then none
    else if block.binds name then some block.path
    else enclosingBinding name outer

/-- Independent characterization of a visible enclosing binder. -/
inductive EnclosingBinding (name : Name) : List BlockContext → BlockPath → Prop where
  | nearest {block outer} (visible : block.lookupBarrier name = false)
      (binds : block.binds name = true) :
      EnclosingBinding name (block :: outer) block.path
  | outside {block outer path} (visible : block.lookupBarrier name = false)
      (skips : block.binds name = false) (found : EnclosingBinding name outer path) :
      EnclosingBinding name (block :: outer) path

inductive Access where
  | moduleName
  | local
  | className
  | declaredGlobal
  | implicitGlobal
  | free (origin : BlockPath)
  | classFree (origin : BlockPath)
  deriving BEq, DecidableEq, Repr

structure Capture where
  name : Name
  origin : BlockPath
  deriving BEq, DecidableEq, Repr

structure Scope where
  context : BlockContext
  accesses : List (Name × Access)
  cells : List Name
  captures : List Capture
  deriving Repr

def Scope.access (scope : Scope) (name : Name) : Option Access :=
  scope.accesses.lookup name

inductive ScopeTree where
  | block (scope : Scope) (children : List ScopeTree)
  deriving Repr

def ScopeTree.scope : ScopeTree → Scope
  | .block scope _ => scope

def ScopeTree.children : ScopeTree → List ScopeTree
  | .block _ children => children

def ScopeTree.atPath (tree : ScopeTree) : BlockPath → Option Scope
  | [] => some tree.scope
  | child :: rest => (tree.children[child]?).bind (fun nested => nested.atPath rest)

inductive Directive where
  | global_
  | nonlocal_
  deriving BEq, DecidableEq, Repr

inductive ScopeError where
  | duplicateParameter (name : Name)
  | parameterDirective (name : Name) (directive : Directive)
  | conflictingDirectives (name : Name)
  | readBeforeDirective (name : Name) (directive : Directive)
  | boundBeforeDirective (name : Name) (directive : Directive)
  | nonlocalInModule (name : Name)
  | unboundNonlocal (name : Name)
  deriving BEq, DecidableEq, Repr

structure Diagnostic where
  path : BlockPath
  error : ScopeError
  deriving BEq, DecidableEq, Repr

end

private inductive CollectedTree where
  | block (context : BlockContext) (children : List CollectedTree)

private def recordName (names : List Name) (name : Name) : List Name :=
  if names.contains name then names else name :: names

private def collectDirective (block : BlockContext) (directive : Directive)
    (name : Name) : Except Diagnostic BlockContext := do
  if block.parameters.contains name then
    throw ⟨block.path, .parameterDirective name directive⟩
  let isGlobal := directive == .global_
  let conflicts := if isGlobal then block.nonlocals else block.globals
  if conflicts.contains name then
    throw ⟨block.path, .conflictingDirectives name⟩
  if block.read.contains name then
    throw ⟨block.path, .readBeforeDirective name directive⟩
  if block.assigned.contains name then
    throw ⟨block.path, .boundBeforeDirective name directive⟩
  if isGlobal then
    return { block with globals := recordName block.globals name }
  if block.kind == .module_ then
    throw ⟨block.path, .nonlocalInModule name⟩
  return { block with nonlocals := recordName block.nonlocals name }

private structure Collecting where
  context : BlockContext
  childrenRev : List CollectedTree := []

private def Collecting.readName (block : Collecting) (name : Name) : Collecting :=
  let read := recordName block.context.read name
  let read := if block.context.kind == .function && name == "super" then
    recordName read "__class__"
  else read
  { block with context := { block.context with read } }

private def Collecting.bindName (block : Collecting) (name : Name) : Collecting :=
  { block with context := { block.context with assigned := recordName block.context.assigned name } }

private def Collecting.childPath (block : Collecting) : BlockPath :=
  block.context.path ++ [block.childrenRev.length]

private def Collecting.addChild (block child : Collecting) : Collecting :=
  let collected := CollectedTree.block child.context child.childrenRev.reverse
  { block with childrenRev := collected :: block.childrenRev }

private def functionContext (path : BlockPath)
    (parameters : List Parameter) : Except Diagnostic BlockContext := do
  let names ← parameters.foldlM (init := []) fun names parameter => do
    if names.contains parameter.name then
      throw ⟨path, .duplicateParameter parameter.name⟩
    return parameter.name :: names
  return { path, kind := .function, parameters := names.reverse }

mutual
  private def collect (block : Collecting) : List Stmt → Except Diagnostic Collecting
    | [] => .ok block
    | stmt :: rest => do collect (← collectStmt block stmt) rest

  private def collectStmt (block : Collecting) : Stmt → Except Diagnostic Collecting
    | .assign target value => do return (← collectExpr block value).bindName target
    | .delete target => .ok (block.bindName target)
    | .expression value | .return_ (some value) => collectExpr block value
    | .pass | .return_ none => .ok block
    | .globalDecl names => do
      let context ← names.foldlM (fun ctx name => collectDirective ctx .global_ name) block.context
      return { block with context }
    | .nonlocalDecl names => do
      let context ← names.foldlM (fun ctx name => collectDirective ctx .nonlocal_ name) block.context
      return { block with context }
    | .if_ condition body otherwise | .while_ condition body otherwise => do
      collect (← collect (← collectExpr block condition) body) otherwise
    | .functionDef name parameters body decorators => do
      let outer ← collectExprs (← collectDefaults block parameters) decorators
      let context ← functionContext outer.childPath parameters
      let nested ← collect { context } body
      return (outer.bindName name).addChild nested
    | .classDef name bases body decorators => do
      let outer ← collectExprs (← collectExprs block decorators) bases
      let nested ← collect { context := { path := outer.childPath, kind := .class_ } } body
      return (outer.bindName name).addChild nested

  private def collectExpr (block : Collecting) : Expr → Except Diagnostic Collecting
    | .name name => .ok (block.readName name)
    | .binary _ left right => do collectExpr (← collectExpr block left) right
    | .call callee arguments => do collectExprs (← collectExpr block callee) arguments
    | .lambda parameters body => do
      let outer ← collectDefaults block parameters
      let context ← functionContext outer.childPath parameters
      let nested ← collectExpr { context } body
      return outer.addChild nested
    | .integer _ | .boolean _ | .none_ => .ok block

  private def collectExprs (block : Collecting) : List Expr → Except Diagnostic Collecting
    | [] => .ok block
    | expr :: rest => do collectExprs (← collectExpr block expr) rest

  private def collectDefaults (block : Collecting) : List Parameter → Except Diagnostic Collecting
    | [] => .ok block
    | ⟨_, none⟩ :: rest => collectDefaults block rest
    | ⟨_, some expr⟩ :: rest => do collectDefaults (← collectExpr block expr) rest
end

private def BlockContext.mentionedNames (block : BlockContext) : List Name :=
  (block.parameters ++ block.assigned.reverse ++ block.read.reverse ++
    block.globals.reverse ++ block.nonlocals.reverse).eraseDups

private def resolveName (block : BlockContext) (outer : List BlockContext)
    (name : Name) : Except Diagnostic (Name × Access) :=
  if block.globals.contains name then .ok (name, .declaredGlobal)
  else if block.kind == .module_ then .ok (name, .moduleName)
  else if block.kind == .function && block.binds name then .ok (name, .local)
  else if block.kind == .class_ && block.assigned.contains name && !block.nonlocals.contains name
    then .ok (name, .className)
  else match enclosingBinding name outer with
    | some path =>
      .ok (name, if block.kind == .class_ then .classFree path else .free path)
    | none =>
      if block.nonlocals.contains name then .error ⟨block.path, .unboundNonlocal name⟩
      else if block.kind == .class_ then .ok (name, .className)
      else .ok (name, .implicitGlobal)

private def directCaptures (accesses : List (Name × Access)) : List Capture :=
  accesses.filterMap fun (name, access) => match access with
    | .free origin | .classFree origin => some ⟨name, origin⟩
    | _ => none

mutual
  private def resolve (outer : List BlockContext) : CollectedTree → Except Diagnostic ScopeTree
    | .block context children => do
      let accesses ← context.mentionedNames.mapM (resolveName context outer)
      let children ← resolveChildren (context :: outer) children
      let fromChildren := children.flatMap (·.scope.captures)
      let (owned, forwarded) := fromChildren.partition (·.origin == context.path)
      let cells := (owned.map (·.name)).eraseDups
      let captures := (directCaptures accesses ++ forwarded).eraseDups
      return .block ⟨context, accesses, cells, captures⟩ children

  private def resolveChildren (outer : List BlockContext) : List CollectedTree → Except Diagnostic (List ScopeTree)
    | [] => .ok []
    | child :: rest => do return (← resolve outer child) :: (← resolveChildren outer rest)
end

/-- Analyze lexical bindings and closure origins for a constructor-level module. -/
public def analyze (source : Module) : Except Diagnostic ScopeTree := do
  let moduleBlock ← collect { context := { path := [], kind := .module_ } } source.body
  resolve [] (.block moduleBlock.context moduleBlock.childrenRev.reverse)

end Silmaril.Languages.Python.Source
