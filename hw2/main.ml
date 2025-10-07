open Assert
open Arg
open X86
open Simulator

exception Ran_tests
let worklist = ref []

let slim_suite = ref (timeout_suite 10 (Studenttests.provided_tests @ Gradedtests.graded_tests))
let full_suite = ref (timeout_suite 10 (Studenttests.provided_tests @ Gradedtests.graded_tests @ Sharedtests.shared_suite))

let exec_tests (suite : suite ref) =
  let o = run_suite !suite in
  Printf.printf "%s\n" (outcome_to_string o);
  raise Ran_tests

let do_one_file fn =
  let _ = Printf.printf "Processing: %s\n" fn in ()

(* Use the --test option to run unit tests and the quit the program. *)
let argspec = [
  (* Arg to unit has to be a function as otherwise ocaml eagerly evaluates the arg, running the tests regardless of input *)
  ("--test", Unit (fun () -> exec_tests slim_suite), "run the test suite, ignoring other inputs");
  ("--full-test", Unit (fun () -> exec_tests full_suite), "run the full test suite, ignoring other inputs");
]

let _ =
  try
    Arg.parse argspec (fun f -> worklist := f :: !worklist)
        "main test harness \n";
    match !worklist with
    | [] -> print_endline "* Nothing to do"
    | _ -> List.iter do_one_file !worklist
  with Ran_tests -> ()
