module

public import Silmaril.Languages.Python.Source.Scope.Defs
import Silmaril.Proofs.Languages.Python.Source.Scope.Thms

public section
namespace Silmaril.Languages.Python.Source

theorem enclosingBinding_eq_some_iff (name : Name) (outer : List BlockContext) (path : BlockPath) :
    enclosingBinding name outer = some path ↔ EnclosingBinding name outer path :=
  Proofs.Languages.Python.Source.Scope.enclosingBinding_eq_some_iff name outer path

theorem enclosingBinding_stops (name : Name) (parent : BlockContext) (outer : List BlockContext)
    (barrier : parent.lookupBarrier name = true) :
    enclosingBinding name (parent :: outer) = none := by
  simp [enclosingBinding, barrier]

theorem enclosingBinding_skips_class (name : Name) (parent : BlockContext)
    (outer : List BlockContext) (kind : parent.kind = .class_) (ordinary : name ≠ "__class__") :
    enclosingBinding name (parent :: outer) = enclosingBinding name outer := by
  simp [enclosingBinding, BlockContext.lookupBarrier, BlockContext.binds, kind, ordinary]

theorem enclosingBinding_classCell (parent : BlockContext) (outer : List BlockContext)
    (kind : parent.kind = .class_) :
    enclosingBinding "__class__" (parent :: outer) = some parent.path := by
  simp [enclosingBinding, BlockContext.lookupBarrier, BlockContext.binds, kind]

theorem Scope.occurrence_access (scope : Scope) (entry : ResolvedOccurrence scope.accesses) :
    scope.access entry.occurrence.name = some entry.access :=
  entry.lookup_eq

/-- Successful scope resolution preserves block metadata, sibling order and all name occurrences. -/
theorem analyze_preserves_lexical {source : Module} {annotations : AnnotationMode}
    {nonlocals : NonlocalPolicy} {tree : ScopeTree}
    (checked : analyze source annotations nonlocals = .ok tree) :
    collectLexical source annotations = .ok tree.lexical :=
  Proofs.Languages.Python.Source.Scope.analyze_preserves_lexical checked

end Silmaril.Languages.Python.Source
