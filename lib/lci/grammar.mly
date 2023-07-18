%{

(** {0} Grammar rules for parser of MiniML *)

open Util
open Ast
open Lexing

let mk_position s e =
  let start_pos = Parsing.rhs_start_pos s in
  { pos_line = start_pos.pos_lnum;
    pos_col = start_pos.pos_cnum - start_pos.pos_bol;
  } 
    
%}

%token <string> IDENT
%token <int> INTVAL
%token <bool> BOOLVAL
%token LPAREN RPAREN 
%token NOT FIX
%token PLUS MINUS DIV TIMES MOD
%token EQ NE LE GE LT GT
%token AND OR ARROW
%token IF ELSE THEN FUN LET REC IN
%token EOF

%start main
%type <Ast.term> main
%%

main:
| term { $1 }
;

ident_list:
| IDENT ident_list { $1 :: $2 }
| IDENT { [$1] }
;
  
primary:
| IDENT { Var ($1, mk_position 1 1) }
| FIX { FunConst (Fix, mk_position 1 1) }
| NOT { FunConst (Not, mk_position 1 1) }
| INTVAL { IntConst ($1, mk_position 1 1) }
| BOOLVAL { BoolConst ($1, mk_position 1 1) }
| LPAREN term RPAREN { $2 }
;

app_term:
| primary { $1 }
| app_term primary { App ($1, $2, mk_position 1 2) }
;
        
mult_term:
| app_term { $1 }
| mult_term mult_op app_term { BinOp ($2, $1, $3, mk_position 1 3) }
;

mult_op:
| TIMES { Mult }
| DIV { Div }
| MOD { Mod }
;
  
add_term:
| mult_term { $1 }
| add_term add_op mult_term { BinOp ($2, $1, $3, mk_position 1 3) }
;

add_op:
| PLUS { Plus }
| MINUS { Minus }
;
    
rel_term:
| add_term { $1 }
| rel_term rel_op add_term { BinOp ($2, $1, $3, mk_position 1 3) }
;

rel_op:
| EQ { Eq }
| LE { Le }
| GE { Ge }
| LT { Lt }
| GT { Gt }
| NE { Ne }
;
    
and_term:
| rel_term { $1 }
| rel_term AND and_term { BinOp (And, $1, $3, mk_position 1 3) }
;

or_term:
| and_term { $1 }
| and_term OR or_term { BinOp (Or, $1, $3, mk_position 1 3) }
;
    
ite_term:
| or_term { $1 }
| IF term THEN term ELSE term { Ite ($2, $4, $6, mk_position 1 6) }
;
    
lambda_term:
| ite_term { $1 }
| FUN ident_list ARROW term {
  List.fold_right
    (fun x t -> Lambda (x, t, mk_position 1 4))
    $2 $4
}
;
    
let_in_term:
| lambda_term { $1 }
| LET REC ident_list EQ term IN term {
  let fn_rec =
    List.fold_right
      (fun x t -> Lambda (x, t, mk_position 1 7))
      $3 $5
  in
  let fn = App (FunConst (Fix, mk_position 1 7), fn_rec, mk_position 1 7) in
  App (Lambda (List.hd $3, $7, mk_position 1 7), fn, mk_position 1 7)
}
| LET ident_list EQ term IN term {
  let fn =
    List.fold_right
      (fun x t -> Lambda (x, t, mk_position 1 6))
      (List.tl $2) $4
  in
  App (Lambda (List.hd $2, $6, mk_position 1 6), fn, mk_position 1 6)
}
;
    
term:
| let_in_term { $1 } 
| error { fail (mk_position 1 1) "Syntax error" }
;
