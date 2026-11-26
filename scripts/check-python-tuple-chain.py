# SPDX-License-Identifier: MIT
"""Check the exact tuple method and equality-chain profile."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

DIRECTORY = Path(__file__).resolve().parents[1] / "tests/languages/python"
SUITE = runpy.run_path(str(DIRECTORY / "source-module-entry/check_seeded_run.py"))
INTAKE = runpy.run_path(str(DIRECTORY / "source-scope/check_intake.py"))
PIN = "tests/python/programs/original/k-python/programs/testtuples3.py"
SHA = "6ebe39b5877a6dcf2bf137915fefa9ed1ed2bb71873552fe37af2bef5b1d77b5"
CONSTRUCTORS_PIN = "tests/python/programs/original/lambda-py/python-reference/tuple/tuple-constructors.py"
CONSTRUCTORS_SHA = "f4c4456ed6ffc8dc95d34f46a18636a57196236e1ff7bafc5cc4b851532adf18"
IMMUTABLE_ALIAS_PIN = "tests/python/programs/original/lambda-py/python-reference/scope/immutable-alias.py"
IMMUTABLE_ALIAS_SHA = "e5c11007f121cac93bfb3cbb9aa9ec74b48ac1e617400434a42b4668b7b9f7ef"

LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.Run.Seeded (legacyListSeed legacyTupleSeed)

private def tupleOutcome (source : Source.Module) (space : Namespace) (status : String)
    (bindings : Bindings) (calls : List (String × Core.Module.SeededCall.Result)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let heap : Core.Closure.Heap := ⟨1, fun address => if address == 0 then some (.int 23) else none⟩
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled heap (lists := lists)
  let completion := match result.completion with
    | .ok () => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error _ => "unexpected completion"
  return completion == status && result.residual.moduleGlobals == bindings &&
    result.residual.builtins == space.builtins && result.lists == lists &&
    result.heap.next == 1 &&
    result.calls.map (fun event => (event.callee, event.observation.result)) == calls &&
    result.calls.all (·.observation.caught.isNone) &&
    (result.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23)

private def tupleTrace (source : Source.Module) (space : Namespace) : Option
    (Except Core.Module.TupleDispatch.Failure Bool × List (Except Core.Module.TupleDispatch.Failure
      Core.Module.TupleDispatch.Object) × Array (List Core.Module.Value)) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let test ← compiled.instructions.findSome? fun
    | .assertTupleChain test => some test
    | _ => none
  let trace := TupleChain.evaluate (fun _ => Compile.ModuleEntry.Functions.Run.Seeded.tupleBinding space) test
  return (trace.result, trace.reached, trace.heap.objects)

private def ordinaryTuple (source : Source.Module) : Option (String × String × String) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  match (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000 compiled.start).2 with
  | .finished session completion =>
    let status := match completion with
      | .normal => "normal"
      | .assertionError => "AssertionError:empty"
      | .raised error => raised (.runtime error)
      | .scalarProfile => "unsupported"
      | _ => "unexpected completion"
    let binding name := resultBinding ((session.globals name).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue)
    some (status, binding "keep", binding "tail")
  | _ => none
"""

STOCK = "(legacyTupleSeed .builtin)"
MASKED = f'({STOCK}.bindGlobal "tuple" .none)'


def assert_equal(left, right):
    assert left == right, (left, right)


def execute(source, builtins, initial=None, expected=None):
    namespace = dict(initial or {}, __builtins__=builtins)
    result = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<tuple fixture>", "exec", dont_inherit=True, optimize=0), namespace)
        except AttributeError as error:
            result = "AttributeError:" + error.name
        except (NameError, TypeError, AssertionError) as error:
            result = SUITE["exception_observation"](error)
    assert not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is builtins
    assert namespace == expected, namespace
    return result


def check(source, source_path, lean_path, *guards):
    INTAKE["emit"](source_path, lean_path, source)
    INTAKE["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])


def outcome(space, result, bindings, calls="[]", source="pythonSource"):
    return f"#guard tupleOutcome {source} {space} {json.dumps(result)} {bindings} {calls}"


def replay_pin(checkout, source_path, lean_path):
    revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    source = SUITE["pinned_source"](checkout, PIN, SHA)
    statement, = ast.parse(source).body
    test = statement.test
    assert type(statement) is ast.Assert and all(type(op) is ast.Eq for op in test.ops)
    operands = [test.left, *test.comparators]
    values = [eval(compile(ast.Expression(expr), PIN, "eval", optimize=0), {"tuple": tuple}) for expr in operands]
    assert values == [(5, 6)] * 4 and all(type(value) is tuple for value in values)
    assert execute(source, {"tuple": tuple}, expected={}) == "normal"
    assert execute(source, {}, expected={}) == "NameError:tuple"
    guards = ['#guard ordinaryTuple pythonSource == some ("NameError:tuple", "absent", "absent")']
    absent = ["empty", "legacy_builtin", "legacy_preamble", *SUITE["OPT_IN_PROFILES"]]
    for profile in absent:
        assert SUITE["cpython"](source, profile, expected_globals={}) == ["NameError:tuple", "absent", "absent"]
        space = f"(initial {json.dumps(profile)})"
        guards.append(outcome(space, "NameError:tuple", f"{space}.moduleGlobals"))
    for placement in ("builtin", "preamble"):
        space = f"(legacyListSeed .{placement})"
        assert execute(source, {"list": list}, expected={}) == "NameError:tuple"
        guards.append(outcome(space, "NameError:tuple", f"{space}.moduleGlobals"))
    for placement in ("builtin", "preamble"):
        space = f"(legacyTupleSeed .{placement})"
        guards.append(outcome(space, "normal", f"{space}.moduleGlobals"))
    objects = ", ".join(f".ok ⟨some {address}, [.int 5, .int 6]⟩" for address in (2, 5, 8, 9))
    guards.extend((
        f"#guard tupleTrace pythonSource {STOCK} == some (.ok true, [{objects}], "
        "#[[.int 5], [.int 6], [.int 5, .int 6], [.int 5], [.int 6], [.int 5, .int 6], "
        "[.int 5], [.int 6], [.int 5, .int 6], [.int 5, .int 6]])",
        "#guard tupleTrace pythonSource Namespace.empty == some (.error .missingType, "
        "[.ok ⟨some 2, [.int 5, .int 6]⟩, .error .missingType], #[[.int 5], [.int 6], [.int 5, .int 6]])",
    ))
    check(source, source_path, lean_path, *guards)
    return {"upstream": revision, "sha256": SHA, "operand_values": values,
            "stock_seeded": "normal", "ordinary_and_prior_seeds": "NameError:tuple"}


def method_controls():
    left, right = tuple([True]), tuple([2])
    empty = ()
    for method in (lambda first, second: first.__add__(second), tuple.__add__, lambda first, second: first + second):
        assert method(left, empty) is left and method(empty, right) is right
        assert method(empty, empty) is empty
        joined = method(left, right)
        assert joined == (True, 2) and joined is not left and joined is not right
        assert type(joined[0]) is bool
    assert left.__eq__([True]) is NotImplemented and tuple.__eq__(left, [True]) is NotImplemented
    assert (left == [True]) is False
    scope = {"left": left}
    assert execute("left.__add__([True])", {}, scope, scope) == "TypeError"

    events = []
    def prepare(name, value):
        events.append(name)
        return value

    assert execute("tuple.__add__(prepare('receiver', (1,)), prepare('argument', (2,)))",
                   {}, {"tuple": None, "prepare": prepare}, {"tuple": None, "prepare": prepare}) == "AttributeError:__add__"
    assert events == []
    scope = {"tuple": tuple, "prepare": prepare}
    assert execute("tuple.__add__(prepare('receiver', []), prepare('argument', (2,)))",
                   {}, scope, scope) == "TypeError"
    assert events == ["receiver", "argument"]
    events.clear()
    scope = {"prepare": prepare}
    assert execute("assert prepare('left', (1,)) == prepare('middle', (1,)) == prepare('right', (2,))"
                   " == prepare('skipped', (2,))", {}, scope, scope) == "AssertionError:empty"
    assert events == ["left", "middle", "right"]
    return {"empty_aliases": True, "cross_kind_method": "NotImplemented",
            "cross_kind_operator": False, "chain_order": events}


def chain_controls(source_path, lean_path):
    outcomes = {}
    cases = (
        ("early_false", "assert (1,).__add__(()) == (2,) == tuple.__add__((2,), ())",
         "Namespace.empty", {}, {}, "AssertionError:empty", "AssertionError:empty",
         "#guard tupleTrace pythonSource Namespace.empty == some "
         "(.ok false, [.ok ⟨some 0, [.int 1]⟩, .ok ⟨some 1, [.int 2]⟩], #[[.int 1], [.int 2]])"),
        ("late_false", "assert (1,).__add__(()) == ().__add__((1,)) == (2,) == tuple.__add__((2,), ())",
         "Namespace.empty", {}, {}, "AssertionError:empty", "AssertionError:empty",
         "#guard tupleTrace pythonSource Namespace.empty == some "
         "(.ok false, [.ok ⟨some 0, [.int 1]⟩, .ok ⟨some 1, [.int 1]⟩, .ok ⟨some 2, [.int 2]⟩], "
         "#[[.int 1], [.int 1], [.int 2]])"),
        ("bound_without_seed", "assert (True,).__add__(()) == (1,)", "Namespace.empty", {}, {},
         "normal", "normal", ""),
        ("operator_empty", "assert (1,).__add__(()) == () + (1,) == (1,) + ()", "Namespace.empty", {}, {},
         "normal", "normal", "#guard tupleTrace pythonSource Namespace.empty == some "
         "(.ok true, [.ok ⟨some 0, [.int 1]⟩, .ok ⟨some 1, [.int 1]⟩, .ok ⟨some 2, [.int 1]⟩], "
         "#[[.int 1], [.int 1], [.int 1]])"),
        ("masked_type", "assert (1,) == tuple.__add__((1,), ())", MASKED, {"tuple": tuple}, {"tuple": None},
         "AttributeError:__add__", "unsupported",
         f"#guard tupleTrace pythonSource {MASKED} == some (.error (.missingAttribute .add), "
         "[.ok ⟨some 0, [.int 1]⟩, .error (.missingAttribute .add)], #[[.int 1]])"),
        ("different_descriptor", "assert (1,) == tuple.__add__((1,), ())",
         f'({STOCK}.bindGlobal "tuple" (.int 0))', {"tuple": tuple}, {"tuple": 0}, "TypeError", "unsupported", ""),
    )
    for name, assertion, space, builtins, initial, python_status, lean_status, trace in cases:
        source = "keep = 7\n" + assertion + "\ntail = 9\n"
        bindings = {"keep": 7, **initial}
        lean_bindings = ['("keep", .int 7)']
        if python_status == "normal":
            bindings["tail"] = 9
            lean_bindings.insert(0, '("tail", .int 9)')
        if initial:
            tag = ".none" if initial["tuple"] is None else ".int 0"
            lean_bindings.append(f'("tuple", {tag})')
        assert execute(source, builtins, initial, bindings) == python_status, name
        guards = [outcome(space, lean_status, "[" + ", ".join(lean_bindings) + "]"), trace]
        if space == "Namespace.empty":
            tail = "int:9" if lean_status == "normal" else "absent"
            guards.append(f"#guard ordinaryTuple pythonSource == some ({json.dumps(lean_status)}, \"int:7\", \"{tail}\")")
        check(source, source_path, lean_path, *guards)
        outcomes[name] = {"cpython": python_status, "lean": lean_status}

    restore = "saved = tuple\ntuple = None\ntuple = saved\nassert tuple.__add__((True,), ()) == (1,)\n"
    assert execute(restore, {"tuple": tuple}, expected={"tuple": tuple, "saved": tuple}) == "normal"
    check(restore, source_path, lean_path,
          outcome(STOCK, "normal", '[("tuple", .builtin .tuple), ("saved", .builtin .tuple)]'))
    ordinary_mask = "keep = 7\ntuple = None\nassert tuple.__add__((1,), ()) == (1,)\ntail = 9\n"
    assert execute(ordinary_mask, {}, expected={"keep": 7, "tuple": None}) == "AttributeError:__add__"
    check(ordinary_mask, source_path, lean_path,
          '#guard ordinaryTuple pythonSource == some ("unsupported", "int:7", "absent")')
    for text in (
        "assert (1,).__add__(()) == (2,) == tuple.__add__((unknown,), ())\n",
        "assert (1,).__add__(()) == (2,) == tuple.__add__(x=(2,), y=())\n",
        "assert tuple.__add__([1], ()) == (1,)\n",
        "assert (1,).__eq__([1]) == ()\n",
    ):
        check(text, source_path, lean_path, """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)""")
    return outcomes


def constructor_controls(source_path, lean_path):
    first = tuple([True, None])
    equal = tuple([1, None])
    assert first == equal and first is not equal
    assert tuple(first) is first and tuple(equal) is equal
    empty = ()
    assert tuple() is empty and tuple(empty) is empty

    assertion = "assert tuple((True, 1, None)) == tuple((1, True, None)) == tuple((1, 1, None))\n"
    source = "keep = 7\n" + assertion + "tail = 9\n"
    assert execute(source, {"tuple": tuple}, expected={"keep": 7, "tail": 9}) == "normal"
    assert execute(source, {}, expected={"keep": 7}) == "NameError:tuple"
    assert execute(source, {"tuple": tuple}, {"tuple": 0}, {"tuple": 0, "keep": 7}) == "TypeError"
    masked = f'({STOCK}.bindGlobal "tuple" (.int 0))'
    check(source, source_path, lean_path,
          outcome(STOCK, "normal", '[("tail", .int 9), ("keep", .int 7)]'),
          outcome("Namespace.empty", "NameError:tuple", '[("keep", .int 7)]'),
          outcome(masked, "TypeError", '[("keep", .int 7), ("tuple", .int 0)]'),
          '#guard ordinaryTuple pythonSource == some ("NameError:tuple", "int:7", "absent")',
          f"#guard tupleTrace pythonSource {STOCK} == some (.ok true, "
          "[.ok ⟨some 0, [.bool true, .int 1, .none]⟩, .ok ⟨some 1, [.int 1, .bool true, .none]⟩, "
          ".ok ⟨some 2, [.int 1, .int 1, .none]⟩], "
          "#[[.bool true, .int 1, .none], [.int 1, .bool true, .none], [.int 1, .int 1, .none]])",
          "#guard tupleTrace pythonSource Namespace.empty == "
          "some (.error .missingType, [.error .missingType], #[])",
          f"#guard tupleTrace pythonSource {masked} == "
          "some (.error .notCallable, [.error .notCallable], #[[.bool true, .int 1, .none]])")

    empty_assertion = "assert tuple() == () == tuple(())\n"
    restore = "saved = tuple\ntuple = None\ntuple = saved\n" + empty_assertion
    bindings = '[("tuple", .builtin .tuple), ("saved", .builtin .tuple)]'
    assert execute(restore, {"tuple": tuple}, expected={"tuple": tuple, "saved": tuple}) == "normal"
    check(restore, source_path, lean_path, outcome(STOCK, "normal", bindings),
          f"#guard tupleTrace pythonSource {STOCK} == "
          "some (.ok true, [.ok ⟨none, []⟩, .ok ⟨none, []⟩, .ok ⟨none, []⟩], #[])")
    masked = "keep = 7\ntuple = None\n" + assertion + "tail = 9\n"
    assert execute(masked, {"tuple": tuple}, expected={"keep": 7, "tuple": None}) == "TypeError"
    check(masked, source_path, lean_path,
          outcome(STOCK, "TypeError", '[("tuple", .none), ("keep", .int 7)]'),
          '#guard ordinaryTuple pythonSource == some ("TypeError", "int:7", "absent")')

    skipped = "assert (0,).__add__(()) == (1,) == tuple((2,))\n"
    assert execute(skipped, {}, expected={}) == "AssertionError:empty"
    check(skipped, source_path, lean_path, outcome("Namespace.empty", "AssertionError:empty", "[]"),
          "#guard tupleTrace pythonSource Namespace.empty == some (.ok false, "
          "[.ok ⟨some 0, [.int 0]⟩, .ok ⟨some 1, [.int 1]⟩], #[[.int 0], [.int 1]])")
    return {"exact_alias": True, "empty_singleton": True, "live_lookup": True}


def replay_empty_constructor(checkout, source_path, lean_path):
    source = SUITE["pinned_source"](checkout, CONSTRUCTORS_PIN, CONSTRUCTORS_SHA)
    first_statement = ast.Module(body=ast.parse(source).body[:1], type_ignores=[])
    empty_tuple = ()

    def equal_empty(left, right):
        assert left is empty_tuple and right is empty_tuple

    def truth(value):
        assert value

    both = {"tuple": tuple, "___assertEqual": equal_empty}
    assert execute(first_statement, both, expected={}) == "normal"
    assert execute(first_statement, {"___assertEqual": equal_empty}, expected={}) == "NameError:tuple"
    assert execute(first_statement, {}, expected={}) == "NameError:___assertEqual"
    assert execute(first_statement, both, {"tuple": 7}, {"tuple": 7}) == "TypeError"
    assert execute(source, {"tuple": tuple, "___assertEqual": assert_equal, "___assertTrue": truth},
                   expected={"t0_3": (0, 1, 2, 3), "t0_3_bis": (0, 1, 2, 3)}) == "normal"

    first = "firstConstructorStatement"
    guards = ["""
private def firstConstructorStatement : Source.Module := ⟨pythonSource.body.take 1⟩
#guard (match Compile.ModuleEntry.Functions.Run.compile firstConstructorStatement with
  | .ok compiled => match compiled.instructions with
    | [.nestedCall .discard "___assertEqual" [.call "tuple" [], .scalar (.tuple [])]] => true
    | _ => false
  | _ => false)
#guard (match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)
#guard ordinaryTuple firstConstructorStatement == some ("NameError:___assertEqual", "absent", "absent")
#guard Core.Module.SeededCall.invoke (.builtin .tuple) [.returnedTuple []] == .error .unsupported
""", outcome("Namespace.empty", "NameError:___assertEqual", "[]", source=first)]
    for placement in ("builtin", "preamble"):
        base = f'(initial "legacy_{placement}")'
        stock = f"(legacyTupleSeed .{placement})"
        guards.extend((
            outcome(base, "NameError:tuple", f"{base}.moduleGlobals",
                    '[("tuple", .error (.raised (.runtime (.nameError "tuple"))))]', first),
            outcome(stock, "normal", f"{stock}.moduleGlobals",
                    '[("tuple", .ok (.returnedTuple [])), ("___assertEqual", .ok .none)]', first),
        ))
    mask = f'({STOCK}.bindGlobal "tuple" (.int 7))'
    guards.append(outcome(mask, "TypeError", f"{mask}.moduleGlobals",
                          '[("tuple", .error (.raised (.runtime .notCallable)))]', first))
    check(source, source_path, lean_path, *guards)

    alias = "saved = tuple\ntuple = 7\nanswer = saved()\nbad = tuple()\n"
    assert execute(alias, {"tuple": tuple},
                   expected={"saved": tuple, "tuple": 7, "answer": empty_tuple}) == "TypeError"
    check(alias, source_path, lean_path, outcome(
        STOCK, "TypeError", '[("answer", .returnedTuple []), ("tuple", .int 7), ("saved", .builtin .tuple)]',
        '[("saved", .ok (.returnedTuple [])), ("tuple", .error (.raised (.runtime .notCallable)))]'))
    return {"sha256": CONSTRUCTORS_SHA, "inner": "canonical empty tuple",
            "stock_seeded_prefix": "normal", "whole_source": "rejected"}


def replay_immutable_alias(checkout, source_path, lean_path):
    source = SUITE["pinned_source"](checkout, IMMUTABLE_ALIAS_PIN, IMMUTABLE_ALIAS_SHA)
    statements = ast.parse(source).body
    assert statements[15].lineno == 21
    prefix = ast.Module(body=statements[:15], type_ignores=[])
    expected = {"x": 2, "y": 3, "t": (1, 2, 3), "t1": (1, 2, 3, 4)}
    helper = {"___assertEqual": assert_equal}
    assert execute(prefix, {}, expected={"x": 2, "y": 1}) == "NameError:___assertEqual"
    assert execute(prefix, helper, expected=expected) == "normal"
    assert execute(prefix, {}, helper, expected | helper) == "normal"

    prefix_term = "beforeTextBinding"
    guards = ["""
private def beforeTextBinding : Source.Module := ⟨pythonSource.body.take 15⟩
#guard (match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)
#guard ordinaryTuple beforeTextBinding == some ("NameError:___assertEqual", "absent", "absent")
"""]
    guards.append(outcome("Namespace.empty", "NameError:___assertEqual", '[("x", .int 2), ("y", .int 1)]',
                          '[("___assertEqual", .error (.raised (.runtime (.nameError "___assertEqual"))))]',
                          prefix_term))
    bindings = ('[("t1", .returnedTuple [.int 1, .int 2, .int 3, .int 4]), '
                '("t", .returnedTuple [.int 1, .int 2, .int 3]), ("y", .int 3), ("x", .int 2)]')
    for placement in ("builtin", "preamble"):
        space = f'(initial "legacy_{placement}")'
        guards.append(outcome(space, "normal", f"({bindings} ++ {space}.moduleGlobals)",
                              '(List.replicate 7 ("___assertEqual", .ok .none))', prefix_term))
    check(source, source_path, lean_path, *guards)
    return {"sha256": IMMUTABLE_ALIAS_SHA, "prefix_statements": len(prefix.body),
            "seeded_prefix": "normal", "whole_source": "rejected at text binding"}


def tuple_helper_controls(source_path, lean_path):
    builtins = {"tuple": tuple, "___assertEqual": assert_equal}
    source = ("saved = ___assertEqual\n___assertEqual = 0\n"
              "saved((True, False, None, -2), (1, 0, None, -2))\n"
              "___assertEqual(tuple(), ())\nunreached = 9\n")
    assert execute(source, builtins, expected={"saved": assert_equal, "___assertEqual": 0}) == "TypeError"
    check(source, source_path, lean_path, outcome(
        STOCK, "TypeError", '[("___assertEqual", .int 0), ("saved", .helper .assertEqual)]',
        '[("saved", .ok .none), ("tuple", .ok (.returnedTuple [])), '
        '("___assertEqual", .error (.raised (.runtime .notCallable)))]'))

    for source, missing, receipts in (
        ("___assertEqual(missing_left, tuple())\n", "missing_left", "[]"),
        ("___assertEqual(tuple(), missing_right)\n", "missing_right", '[("tuple", .ok (.returnedTuple []))]'),
    ):
        assert execute(source, builtins, expected={}) == f"NameError:{missing}"
        check(source, source_path, lean_path, outcome(STOCK, f"NameError:{missing}", "[]", receipts))

    for left, right, left_lean, right_lean in (
        ((True, None), (1, 0), "[.bool true, .none]", "[.int 1, .int 0]"),
        ((), (False,), "[]", "[.bool false]"),
        ((1, 2), (2, 1), "[.int 1, .int 2]", "[.int 2, .int 1]"),
    ):
        source = f"___assertEqual({left!r}, {right!r})\nunreached = 9\n"
        namespace = {"__builtins__": builtins}
        try:
            exec(compile(source, "<tuple mismatch>", "exec", dont_inherit=True, optimize=0), namespace)
        except AssertionError as error:
            got_left, got_right = error.args[0]
            assert error.args == ((left, right),) and set(namespace) == {"__builtins__"}
            for actual, expected in ((got_left, left), (got_right, right)):
                assert [(type(item), item) for item in actual] == [(type(item), item) for item in expected]
        else:
            raise AssertionError("tuple mismatch completed")
        failure = f".assertionError (.tuplePair {left_lean} {right_lean})"
        check(source, source_path, lean_path,
              f'#guard tupleOutcome pythonSource {STOCK} (raised ({failure})) [] '
              f'[("___assertEqual", .error (.raised ({failure})))]')
    return {"numeric_scalar_equality": True, "failure_payloads": True, "callee_and_operand_order": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True)
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Fixture.py"
        lean = source.with_suffix(".lean")
        evidence = {"cpython": sys.version.split()[0], "pin": replay_pin(args.upstream, source, lean),
                    "methods": method_controls(), "chains": chain_controls(source, lean),
                    "constructors": constructor_controls(source, lean),
                    "linked_empty_constructor": replay_empty_constructor(args.upstream, source, lean),
                    "immutable_alias": replay_immutable_alias(args.upstream, source, lean),
                    "tuple_helper": tuple_helper_controls(source, lean)}
    print(json.dumps(evidence))
