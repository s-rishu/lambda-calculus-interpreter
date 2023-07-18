(** {0} Entry point of MiniML interpreter *)

open Lci
open Util
open Ast
open Eval


let usage_message =
  "MiniML interpreter\n" ^
  "\nUsage:\n  " ^ Sys.argv.(0) ^ 
  " <input file> [options]\n"

let verbose = ref false
let call_by_name = ref false
let bonus = ref false
    
let cmd_options_spec =
  [("-v", Arg.Set verbose, " Display debug messages");
   ("-call-by-name", Arg.Set call_by_name, " Interpret program using call-by-name semantics (default is call-by-value)");
   ("-bonus", Arg.Set bonus, " Interpret program using environment-based interpreter (bonus part)")]

let cmd_line_error msg =
  Arg.usage (Arg.align cmd_options_spec) usage_message;
  failwith ("\nCommand line error: " ^ msg)
    
let () =
  try
    let input_file = ref "" in
    let set_file s =
      input_file := s
    in
    let _ = Arg.parse cmd_options_spec set_file usage_message in
    if !input_file = ""
    then cmd_line_error "input file missing"
    else begin
      let prog = Parser.parse_from_file !input_file in
      let _ =
        find_free_var prog |>
        Option.map (fun (x, pos) -> fail pos ("Unbound value " ^ x))
      in
      let _ =
        if !verbose then begin
          print_endline "Evaluating:";
          print_term stdout prog;
          print_string "\nResult: ";
        end
      in
      let eval =
        if !call_by_name then eval_by_name else
        if !bonus then eval_with_envs else eval_by_value
      in
      let v = eval prog in
      print_endline (string_of_value v)
    end
  with
  | Failure s ->
      let bs = if !verbose then Printexc.get_backtrace () else "" in
      output_string stderr (s ^ "\n" ^ bs); exit 1
