module

public import Silmaril.Languages.Python.Core.Module.Dictionary.Defs

public section

namespace Silmaril.Languages.Python.Core.Module.Dictionary

theorem insert_replaces {first entry : Entry} (rest : List Entry)
    (same : first.1.equal entry.1 = true) :
    insert entry (first :: rest) = (first.1, entry.2) :: rest := by simp [insert, same]

theorem insert_keeps {first entry : Entry} (rest : List Entry)
    (different : first.1.equal entry.1 = false) :
    insert entry (first :: rest) = first :: insert entry rest := by simp [insert, different]

theorem build_snoc (display : List Entry) (entry : Entry) :
    build (display ++ [entry]) = insert entry (build display) := by simp [build, List.foldl_append]

theorem Get.eval_missing (test : Get) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) (missing : globals test.receiver = none) :
    test.eval globals resolve = .error (.missingName test.receiver) := by simp [Get.eval, readName, missing, bind, Except.bind]

theorem Get.eval_default_error (test : Get) (globals : String → Option ReadValue)
    (resolve : Object → Option (List Entry)) (object : Object) (entries : List Entry) (key : ReadValue)
    (found : globals test.receiver = some (.object object)) (live : resolve object = some entries)
    (prepared : test.key.read globals = .ok key) {error : Failure}
    (failed : test.fallback.read globals = .error error) :
    test.eval globals resolve = .error error := by simp [Get.eval, readName, found, live, prepared, failed, bind, Except.bind]

end Silmaril.Languages.Python.Core.Module.Dictionary
