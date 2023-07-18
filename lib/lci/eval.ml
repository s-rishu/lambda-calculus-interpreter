(** {0} The evaluation function of the MiniML interpreter. *)
  
open Ast
open Util

(** Generated a type error at position [pos] for expected type [exp_typ] and actual type [act_typ]. *)
let type_error pos exp_typ act_typ =
  fail pos (Printf.sprintf "Type mismatch\n  Expected type: %s\n  Actual type: %s" exp_typ act_typ)
  
(** Extract bool from a BoolVal. Generate type error message if value is not a BoolVal *)
let bool_of_value pos = function
  | BoolVal b -> b
  | IntVal i -> type_error pos "bool" "int"
  | Closure _ -> type_error pos "bool" "function"

(** Extract int from an IntVal. Generate type error message if value is not an IntVal *)
let int_of_value pos = function
  | IntVal i -> i
  | BoolVal _ -> type_error pos "int" "bool"
  | Closure _ -> type_error pos "int" "function"

(** Extract closure components from a Closure value. Generate type error message if value is not a Closure *)
let closure_of_value pos = function
  | Closure (x, t, env) -> x, t, env
  | IntVal _ -> type_error pos "function" "int"
  | BoolVal _ -> type_error pos "function" "bool"

(** Convert a value back to a term *)
let term_of_value pos = function
  | IntVal i -> IntConst (i, pos)
  | BoolVal b -> BoolConst (b, pos)
  | Closure (x, t, _) -> Lambda (x, t, pos)
        
(** Evaluate term t to a value using call-by-value semantics *)
let eval beta (t: term) : value =
  let rec eval t = match t with
  | FunConst (Fix, pos) ->
      let f = Var ("f", pos) in
      let x = Var ("x", pos) in
      let fn =
        Lambda ("x",
                App (App (f, App (t, f, pos), pos),
                     x, pos),
                pos)
      in
      Closure ("f", fn, [])
  | FunConst (Not, pos) ->
      let x = Var ("x", pos) in
      let fn = Lambda ("x", App (t, x, pos), pos) in
      Closure ("x", fn, [])
  | IntConst (i, _) -> IntVal i
  | BoolConst (b, _) -> BoolVal b
  | App (FunConst (Not, _), t, pos) ->
      if (bool_of_value pos (eval t)) then (BoolVal (false)) else (BoolVal (true))
  | App (t1, t2, pos) ->
      (* Evaluate function application. The actual work is delegated to the function beta. *)
      beta t1 t2 pos
  | BinOp (bop, t1, t2, pos) -> (
        match bop with
           | Mult  -> IntVal ((int_of_value pos (eval t1)) * (int_of_value pos (eval t2)))
           | Div   -> IntVal ((int_of_value pos (eval t1)) / (int_of_value pos (eval t2)))
           | Mod   -> IntVal ((int_of_value pos (eval t1)) mod (int_of_value pos (eval t2)))
           | Plus  -> IntVal ((int_of_value pos (eval t1)) + (int_of_value pos (eval t2)))
           | Minus -> IntVal ((int_of_value pos (eval t1)) - (int_of_value pos (eval t2)))
           | Eq    -> BoolVal ((eval t1) = (eval t2))
           | Ne    -> BoolVal ((eval t1) <> (eval t2))
           | Lt    -> BoolVal ((int_of_value pos (eval t1)) < (int_of_value pos (eval t2)))
           | Gt    -> BoolVal ((int_of_value pos (eval t1)) > (int_of_value pos (eval t2)))
           | Le    -> BoolVal ((int_of_value pos (eval t1)) <= (int_of_value pos (eval t2)))
           | Ge    -> BoolVal ((int_of_value pos (eval t1)) >= (int_of_value pos (eval t2)))
           | And   -> BoolVal ((bool_of_value pos (eval t1)) && (bool_of_value pos (eval t2)))
           | Or    -> BoolVal ((bool_of_value pos (eval t1)) || (bool_of_value pos (eval t2)))
           )
  | Ite (t1, t2, t3, pos) ->
      if (bool_of_value pos (eval t1)) then (eval t2) else (eval t3)
  | Lambda (x, t, _) ->
      Closure (x, t, [])
  | Var (x, pos) ->
      (* This case should never be reachable assuming that the input term is closed 
       * and substitution is implemented correctly. *)
      fail pos "unexpected free variable"
  in
  eval t

(** beta-reduction step using applicative-order (call-by-value) semantics *)
let rec beta_call_by_value (t1: term) (t2: term) (pos: pos) : value =
  let arg2 = eval beta_call_by_value t2
  in (
  match (eval beta_call_by_value t1) with
    | Closure (x, t, _) -> eval beta_call_by_value (subst t x (term_of_value pos arg2))
    | _ as v-> v
  )

(** Evaluate term t to a value using applicative-order (call-by-value) semantics *)
let eval_by_value (t: term) : value = eval beta_call_by_value t


(** beta-reduction step using normal-order (call-by-name) semantics *)
let rec beta_call_by_name  (t1: term) (t2: term) (pos: pos) : value =
  match (eval beta_call_by_name t1) with
    | Closure (x, t, _) -> eval beta_call_by_name (subst t x t2)
    | _ as v -> v
    

(** Evaluate term t to a value using normal-order (call-by-name) semantics *)
let eval_by_name (t: term) : value = eval beta_call_by_name t

(** {1} Bonus part *)
    
(** Evaluate term t using value environments instead of substitutions *)
let eval_with_envs (t: term) : value =
  let rec eval (env: env) (t: term) = 
    match t with
      | FunConst (Fix, pos) ->
          let f = Var ("f", pos) in
          let x = Var ("x", pos) in
          let fn =
            Lambda ("x",
                    App (App (f, App (t, f, pos), pos),
                         x, pos),
                    pos)
          in
          Closure ("f", fn, env)
      | FunConst (Not, pos) ->
          let x = Var ("x", pos) in
          let fn = Lambda ("x", App (t, x, pos), pos) in
          Closure ("x", fn, env)
      | IntConst (i, _) -> IntVal i
      | BoolConst (b, _) -> BoolVal b
      | App (FunConst (Not, _), t, pos) ->
          if (bool_of_value pos (eval env t)) then (BoolVal (false)) else (BoolVal (true))
      | App (t1, t2, _) -> (
          match eval env t1 with
            | Closure(x, t, env1) -> eval ((x, eval env t2)::env1) t
            | _ as t -> t
            )
      | BinOp (bop, t1, t2, pos) -> (
            match bop with
               | Mult  -> IntVal ((int_of_value pos (eval env t1)) * (int_of_value pos (eval env t2)))
               | Div   -> IntVal ((int_of_value pos (eval env t1)) / (int_of_value pos (eval env t2)))
               | Mod   -> IntVal ((int_of_value pos (eval env t1)) mod (int_of_value pos (eval env t2)))
               | Plus  -> IntVal ((int_of_value pos (eval env t1)) + (int_of_value pos (eval env t2)))
               | Minus -> IntVal ((int_of_value pos (eval env t1)) - (int_of_value pos (eval env t2)))
               | Eq    -> BoolVal ((eval env t1) = (eval env t2))
               | Ne    -> BoolVal ((eval env t1) <> (eval env t2))
               | Lt    -> BoolVal ((int_of_value pos (eval env t1)) < (int_of_value pos (eval env t2)))
               | Gt    -> BoolVal ((int_of_value pos (eval env t1)) > (int_of_value pos (eval env t2)))
               | Le    -> BoolVal ((int_of_value pos (eval env t1)) <= (int_of_value pos (eval env t2)))
               | Ge    -> BoolVal ((int_of_value pos (eval env t1)) >= (int_of_value pos (eval env t2)))
               | And   -> BoolVal ((bool_of_value pos (eval env t1)) && (bool_of_value pos (eval env t2)))
               | Or    -> BoolVal ((bool_of_value pos (eval env t1)) || (bool_of_value pos (eval env t2)))
               )
      | Ite (t1, t2, t3, pos) ->
          if (bool_of_value pos (eval env t1)) then (eval env t2) else (eval env t3)
      | Lambda (x, t, _) ->
          Closure (x, t, env)
      | Var (x, pos) ->
          let rec search x = function
              |[] -> IntVal (-1)
              |(hd, v) :: tl -> if hd = x then v else search x tl
          in (search x env)
  in
  eval [] t
