open OUnit2
open Lci
open Util
open Ast

let find_free_var_tests =
  [("2", None);
   ("2 + 3 * 5 mod 2", None);
   ("fun x -> fun y -> y * (x + 3)", None);
   ("f 2 3", Some ("f", { pos_line = 1; pos_col = 0 }));
   ("if (b && not c) && d then 1 else 2", Some ("b", { pos_line = 1; pos_col = 4 }));
   ("fun x -> y * (x + 3)", Some ("y", { pos_line = 1; pos_col = 9 }))]
 
let find_free_var_suite =
  List.map (fun (ts, res) ->
    let t = Parser.parse_from_string ts in
    let print = function
      | None -> "None"
      | Some (v, { pos_line = l; pos_col = c }) ->
          Printf.sprintf "Some (%s, { pos_line = %d; pos_col = %d })" v l c
    in
    let name = "find_free_var (" ^ ts ^ ")" in
    name >::
    fun tc ->
      assert_equal ~printer:print res (find_free_var t))
    find_free_var_tests

let subst_tests =
  ["2", "x", "2 + 3 * 5 mod 2", "2";
   "2 + 3 * 5 mod 2", "y", "2 + 3 * 5 mod 2", "2 + 3 * 5 mod 2";
   "x", "y", "2", "x";
   "x", "x", "2", "2";
   "x + y", "x", "2 + 1", "(2 + 1) + y";
   "x + y", "y", "2 + 1", "x + (2 + 1)";
   "x + x", "x", "2 + 1", "(2 + 1) + (2 + 1)";
   "fun x -> x + y", "y", "2 + 1", "fun x -> x + (2 + 1)";
   "fun x -> x + y", "x", "2 + 1", "fun x -> x + y";
   "fun x -> fun y -> y * (x + 3)", "x", "2 + 3 * 5 mod 2", "fun x -> fun y -> y * (x + 3)";
   "fun x -> fun y -> y * (x + 3)", "y", "2 + 3 * 5 mod 2", "fun x -> fun y -> y * (x + 3)";
   "fun z -> fun y -> y * (x + 3)", "x", "2 + 3 * 5 mod 2", "fun z -> fun y -> y * ((2 + 3 * 5 mod 2) + 3)";
   "f 2 3", "f", "fun x -> fun y -> y * (x + 3)", "(fun x -> fun y -> y * (x + 3)) 2 3";
   "fun y -> x * x", "x", "2", "fun y -> 2 * 2";
   "(fun y -> ((x mod 2) * x)) x", "x", "2", "(fun y -> ((2 mod 2) * 2)) 2";
   "(fun x -> ((x mod 2) * x)) x", "x", "2", "(fun x -> ((x mod 2) * x)) 2"
 ]
    
let subst_suite =
  List.map (fun (t1s, x, t2s, ress) ->
    let t1 = Parser.parse_from_string t1s in
    let t2 = Parser.parse_from_string t2s in
    let res = Parser.parse_from_string ress in
    let name = "subst (" ^ t1s ^ ") " ^ x ^ " (" ^ t2s ^ ")" in
    name >::
    fun tc ->
      assert_equal ~cmp:equal ~printer:string_of_term res (subst t1 x t2))
    subst_tests

let eval_by_value_tests =
  ["2 + 2", "4";
   "2 + -2", "0";
   "2 - 2", "0";
   "2 - 5", "-3";
   "2 * 3", "6";
   "4 / 2", "2";
   "4 / 3", "1";
   "4 mod 3", "1";
   "4 mod -3", "1";
   "4 > 4", "false";
   "6 > -10", "true";
   "4 = 3", "false";
   "4 = 4", "true";
   "not (2 > 1)", "false";
   "not (2 = 1)", "true";
   "true && true", "true";
   "false && true", "false";
   "false && (2 / 0 > 0)", "false"; (* beware of short-circuiting *)
   "true || false", "true";
   "false || false", "false";
   "false || true", "true";
   "true || (2 / 0 > 0)", "true"; (* beware of short-circuiting *)
   "if 2 >= 2 then 4 else 2", "4";
   "if 2 <= 2 then 4 else 2 / 0", "4"; (* beware of short-circuiting *)
   "if 2 <= -1 then 4 / 0 else 2 + 1", "3"; (* beware of short-circuiting *)
   "(fun x -> x + x) 2", "4";
   "(fun x y -> x + y) 2 1", "3";
   "(fun x y -> x y + 1) (fun x -> 2 * x) 2", "5";
   "(fun x -> x) (fun x -> x)", "(fun x -> x)";
   "(fun x -> x) (fun x -> x + 2) 3", "5";
   "let rec fac n = if n = 0 then 1 else n * fac (n - 1) in fac 5", "120";
   "(fun f -> (fun x n -> f (x x) n) (fun x n -> f (x x) n)) (fun fac n -> if n = 0 then 1 else n * fac (n - 1)) 5", "120"
 ]
    
let eval_by_name_tests =
  ["2 + 2", "4";
   "2 + -2", "0";
   "2 - 2", "0";
   "2 - 5", "-3";
   "2 * 3", "6";
   "4 / 2", "2";
   "4 / 3", "1";
   "4 mod 3", "1";
   "4 mod -3", "1";
   "4 > 4", "false";
   "6 > -10", "true";
   "4 = 3", "false";
   "4 = 4", "true";
   "not (2 > 1)", "false";
   "not (2 = 1)", "true";
   "true && true", "true";
   "false && true", "false";
   "false && (2 / 0 > 0)", "false"; (* beware of short-circuiting *)
   "true || false", "true";
   "false || false", "false";
   "false || true", "true";
   "true || (2 / 0 > 0)", "true"; (* beware of short-circuiting *)
   "if 2 >= 2 then 4 else 2", "4";
   "if 2 <= 2 then 4 else 2 / 0", "4"; (* beware of short-circuiting *)
   "if 2 <= -1 then 4 / 0 else 2 + 1", "3"; (* beware of short-circuiting *)
   "(fun x -> x + x) 2", "4";
   "(fun x y -> x + y) 2 1", "3";
   "(fun y -> 2 + 2) (1 / 0)", "4"; (* beware of call-by-name *)
   "(fun x y -> x + x) 2 (1 / 0)", "4"; (* beware of call-by-name *)
   "(fun x y -> x y + 1) (fun x -> 2 * x) 2", "5";
   "(fun x -> 1) ((fun x -> x x) (fun x -> x x))", "1"; (* beware of call-by-name *)
   "(fun f -> (fun x n -> f (x x) n) (fun x n -> f (x x) n)) (fun fac n -> if n = 0 then 1 else n * fac (n - 1)) 5", "120";
   "(fun f -> (fun x -> f (x x)) (fun x -> f (x x))) (fun fac n -> if n = 0 then 1 else n * fac (n - 1)) 5", "120" (* beware of call-by-name *)
 ]
    
let eval_suite eval_name eval tests =
  List.map (fun (ts, ress) ->
    let t = Parser.parse_from_string ts in
    let res = Parser.parse_from_string ress in
    let name = eval_name ^ " (" ^ ts ^ ")" in
    name >::
    fun tc ->
      assert_equal ~cmp:equal ~printer:string_of_term res (eval t |> Eval.term_of_value (position_of_term t)))
    tests

let eval_env_tests =
  ["../../../tests/test01.ml", "7";
   "../../../tests/test02.ml", "5";
   "../../../tests/test03.ml", "5";
   "../../../tests/test04.ml", "15";
   "../../../tests/test05.ml", "5";
   "../../../tests/test06.ml", "120";
   "../../../tests/test09.ml", "1";
   "../../../tests/church.ml", "120"]
    
let eval_env_suite =
  print_endline (Sys.getcwd ());
  List.map (fun (input_file, ress) ->
    let prog = Parser.parse_from_file input_file in
    let res = Parser.parse_from_string ress in
    let name = "eval_with_envs: " ^ input_file in
    name >::
    fun tc ->
      assert_equal ~cmp:equal ~printer:string_of_term
        res
        (Eval.eval_with_envs prog |> Eval.term_of_value (position_of_term prog))) eval_env_tests

let suite =
  "Problem 2 suite" >:::
  find_free_var_suite @
  subst_suite @
  eval_suite "eval_by_value" Eval.eval_by_value eval_by_value_tests @
  eval_suite "eval_by_name" Eval.eval_by_name eval_by_name_tests @ eval_env_suite

let () = run_test_tt_main suite

