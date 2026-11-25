module

import Silmaril.Languages.Python.Source.Scope.Thms
meta import Silmaril.Languages.Python.Source.Scope.Defs
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python.Source

private def inspect (body : List Stmt) (path : BlockPath) (name : Name) : Option Access :=
  (analyze ⟨body⟩).toOption.bind fun tree => (tree.atPath path).bind (·.access name)

private def closedOverLaterBinding : List Stmt :=
  [.functionDef "outer" [] [
    .functionDef "middle" [] [
      .functionDef "inner" [] [.return_ (some (.name "x"))]],
    .assign "x" (.integer 1)]]

#guard inspect closedOverLaterBinding [0, 0, 0] "x" == some (.free [0])
#guard inspect closedOverLaterBinding [0] "x" == some .local
#guard ((analyze ⟨closedOverLaterBinding⟩).toOption.bind (·.atPath [0])).map (·.cells) ==
  some ["x"]
#guard ((analyze ⟨closedOverLaterBinding⟩).toOption.bind (·.atPath [0, 0])).map (·.captures) ==
  some [⟨"x", [0]⟩]

private def shadowedBinding : List Stmt :=
  [.functionDef "outer" [⟨"x", none⟩] [
    .functionDef "middle" [⟨"x", none⟩] [
      .functionDef "inner" [] [.nonlocalDecl ["x"], .assign "x" (.integer 2)]]]]

#guard inspect shadowedBinding [0, 0, 0] "x" == some (.free [0, 0])
#guard ((analyze ⟨shadowedBinding⟩).toOption.bind (·.atPath [0])).map (·.cells) == some []
#guard ((analyze ⟨shadowedBinding⟩).toOption.bind (·.atPath [0, 0])).map (·.cells) == some ["x"]

private def barriers : List Stmt :=
  [.assign "m" (.integer 0), .functionDef "outer" [⟨"x", none⟩] [
    .functionDef "middle" [] [
      .globalDecl ["x"],
      .functionDef "inner" [] [
        .expression (.name "x"), .expression (.name "m")]]]]

#guard inspect barriers [] "m" == some .moduleName
#guard inspect barriers [0, 0] "x" == some .declaredGlobal
#guard inspect barriers [0, 0, 0] "x" == some .implicitGlobal
#guard inspect barriers [0, 0, 0] "m" == some .implicitGlobal

private def defaultsAndControl : List Stmt :=
  [.functionDef "outer" [] [
    .if_ (.name "guard")
      [.functionDef "left" [⟨"p", some (.call (.name "make") [.name "x"])⟩]
        [.return_ (some (.name "p"))]]
      [.functionDef "right" [] [.pass]],
    .while_ (.boolean false) [.delete "x"] [.pass]]]

#guard inspect defaultsAndControl [0] "x" == some .local
#guard inspect defaultsAndControl [0] "make" == some .implicitGlobal
#guard inspect defaultsAndControl [0, 0] "p" == some .local
#guard inspect defaultsAndControl [0, 0] "make" == none
#guard ((analyze ⟨defaultsAndControl⟩).toOption.bind (·.atPath [0, 1])).map (·.context.path) ==
  some [0, 1]
#guard ((analyze ⟨defaultsAndControl⟩).toOption.bind (·.atPath [0, 2])).isNone

private def diagnose (body : List Stmt) : Option Diagnostic :=
  match analyze ⟨body⟩ with
  | .error diagnostic => some diagnostic
  | .ok _ => none

#guard diagnose [.nonlocalDecl ["x"]] == some ⟨[], .nonlocalInModule "x"⟩
#guard diagnose [.assign "x" (.integer 1), .functionDef "f" [] [.nonlocalDecl ["x"]]] ==
  some ⟨[0], .unboundNonlocal "x"⟩
#guard diagnose [.functionDef "f" [⟨"x", none⟩, ⟨"x", none⟩] []] ==
  some ⟨[0], .duplicateParameter "x"⟩
#guard diagnose [.functionDef "f" [⟨"x", none⟩] [.globalDecl ["x"]]] ==
  some ⟨[0], .parameterDirective "x" .global_⟩
#guard diagnose [.functionDef "f" [] [.globalDecl ["x"], .nonlocalDecl ["x"]]] ==
  some ⟨[0], .conflictingDirectives "x"⟩
#guard diagnose [.functionDef "f" [] [.expression (.name "x"), .globalDecl ["x"]]] ==
  some ⟨[0], .readBeforeDirective "x" .global_⟩
#guard diagnose [.functionDef "f" [] [.delete "x", .globalDecl ["x"]]] ==
  some ⟨[0], .boundBeforeDirective "x" .global_⟩
#guard diagnose [.functionDef "f" [] [.globalDecl ["x"], .globalDecl ["x"]]] == none
#guard diagnose [.functionDef "outer" [⟨"x", none⟩] [
  .functionDef "middle" [] [
    .globalDecl ["x"], .functionDef "inner" [] [.nonlocalDecl ["x"]]]]] ==
  some ⟨[0, 0, 0], .unboundNonlocal "x"⟩

private def classScopes : List Stmt :=
  [.functionDef "outer" [⟨"x", none⟩, ⟨"y", none⟩, ⟨"z", none⟩] [
    .classDef "C" [.name "base"] [
      .globalDecl ["y"],
      .assign "x" (.integer 0),
      .expression (.name "z"),
      .expression (.name "unbound"),
      .functionDef "method" [⟨"self", none⟩] [
        .expression (.name "x"), .expression (.name "y"),
        .return_ (some (.call (.name "super") []))],
      .classDef "Nested" [] [
        .expression (.name "__class__"),
        .functionDef "owner" [⟨"self", none⟩] [.return_ (some (.name "__class__"))]]]]]

#guard inspect classScopes [0] "base" == some .implicitGlobal
#guard inspect classScopes [0, 0] "base" == none
#guard inspect classScopes [0, 0] "x" == some .className
#guard inspect classScopes [0, 0] "y" == some .declaredGlobal
#guard inspect classScopes [0, 0] "z" == some (.classFree [0])
#guard inspect classScopes [0, 0] "unbound" == some .className
#guard inspect classScopes [0, 0, 0] "x" == some (.free [0])
#guard inspect classScopes [0, 0, 0] "y" == some (.free [0])
#guard inspect classScopes [0, 0, 0] "__class__" == some (.free [0, 0])
#guard inspect classScopes [0, 0, 1] "__class__" == some (.classFree [0, 0])
#guard inspect classScopes [0, 0, 1, 0] "__class__" == some (.free [0, 0, 1])
#guard ((analyze ⟨classScopes⟩).toOption.bind (·.atPath [0, 0])).map (·.cells) ==
  some ["__class__"]

private def classNonlocal : List Stmt :=
  [.functionDef "outer" [⟨"x", none⟩] [
    .classDef "C" [] [.nonlocalDecl ["x"], .assign "x" (.integer 2)]]]

#guard inspect classNonlocal [0, 0] "x" == some (.classFree [0])
#guard diagnose [.classDef "C" [] [.nonlocalDecl ["missing"]]] ==
  some ⟨[0], .unboundNonlocal "missing"⟩

private def lambdaScopes : List Stmt :=
  [.functionDef "outer" [⟨"x", none⟩, ⟨"y", none⟩] [
    .functionDef "f" [⟨"p", some (.lambda [] (.name "x"))⟩] [
      .return_ (some
        (.lambda [⟨"q", some (.name "p")⟩] (.binary .add (.name "q") (.name "p"))))]
      [.lambda [] (.name "y")]]]

#guard inspect lambdaScopes [0, 0] "x" == some (.free [0])
#guard inspect lambdaScopes [0, 1] "y" == some (.free [0])
#guard inspect lambdaScopes [0, 2] "p" == some .local
#guard inspect lambdaScopes [0, 2, 0] "p" == some (.free [0, 2])
#guard inspect lambdaScopes [0, 2, 0] "q" == some .local
#guard inspect lambdaScopes [0] "<lambda>" == none
#guard ((analyze ⟨lambdaScopes⟩).toOption.bind (·.atPath [0, 2])).map (·.cells) ==
  some ["p"]
#guard diagnose [.expression (.lambda [⟨"x", none⟩, ⟨"x", none⟩] (.name "x"))] ==
  some ⟨[0], .duplicateParameter "x"⟩

private def classHeaderScopes : List Stmt :=
  [.classDef "C" [.lambda [] (.name "baseName")] [.pass] [.lambda [] (.name "decoratorName")]]

#guard inspect classHeaderScopes [0] "decoratorName" == some .implicitGlobal
#guard inspect classHeaderScopes [1] "baseName" == some .implicitGlobal
#guard ((analyze ⟨classHeaderScopes⟩).toOption.bind (·.atPath [2])).map (·.context.kind) ==
  some .class_

#print axioms enclosingBinding_eq_some_iff
#print axioms enclosingBinding_stops
#print axioms enclosingBinding_skips_class
#print axioms enclosingBinding_classCell
