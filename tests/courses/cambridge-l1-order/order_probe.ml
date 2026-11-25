open L1_ocaml

let report layer name result history =
  Printf.printf "EX11 %s %s %s %s\n" layer name result
    (String.concat "," (List.map string_of_int history))

let rec run fuel history ((expr, store) as config) =
  let history = List.assoc "l" store :: history in
  match reduce config with
  | None -> (expr, List.rev history)
  | Some next when fuel > 0 -> run (fuel - 1) history next
  | Some _ -> failwith "L1 step budget exhausted"

let object_check name expr =
  let final, history = run 8 [] (expr, [("l", 0)]) in
  let result =
    match final with
    | Integer n -> string_of_int n
    | Boolean b -> string_of_bool b
    | Skip -> "skip"
    | _ -> failwith "L1 did not return a value"
  in
  report "l1" name result history

let host_check name evaluate =
  let writes = ref [] in
  let mark n =
    writes := n :: !writes;
    0
  in
  let result = evaluate mark in
  report "host" name result (List.rev !writes)

let () =
  let write n = Assign ("l", Integer n) in
  let operand n = Seq (write n, Integer 0) in
  object_check "plus" (Op (operand 1, Plus, operand 2));
  object_check "ge" (Op (operand 1, GTEQ, operand 2));
  object_check "seq" (Seq (write 1, write 2));
  host_check "plus" (fun mark -> string_of_int (mark 1 + mark 2));
  host_check "ge" (fun mark -> string_of_bool (mark 1 >= mark 2));
  host_check "seq" (fun mark -> ignore (mark 1); ignore (mark 2); "skip")
