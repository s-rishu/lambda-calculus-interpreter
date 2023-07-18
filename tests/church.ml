let ctrue = fun x y -> x in
let cfalse = fun x y -> y in

let ite = fun b x y -> b x y in

let cand = fun a b -> ite a b cfalse in

let cor = fun a b -> ite a ctrue b in

let cnot = fun a x y -> a y x in

let zero  = fun s z -> z in
let one   = fun s z -> s z in
let two   = fun s z -> s (s z) in
let three = fun s z -> s (s (s z)) in
let four  = fun s z -> s (s (s (s z))) in
let five  = fun s z -> s (s (s (s (s z)))) in

let succ = fun n s z -> s (n s z) in
let plus = fun n m -> n succ m in

let mult = fun n m -> n (plus m) zero in

let pair = fun x y -> fun b -> b x y in
let fst = fun p -> p ctrue in
let snd = fun p -> p cfalse in

let is_zero = fun n -> n (fun _ -> cfalse) ctrue in
    
let pred = fun n -> snd (n (fun p -> pair (succ (fst p)) (fst p)) (pair zero zero)) in

let fac_fun = fun fac n -> ite (is_zero n) one (mult n (fac (pred n))) in

(* approximations of fatorial obtained from fac_fun *)
let fac0 = fun n -> 0 in
let fac1 = fac_fun fac0 in
let fac2 = fac_fun fac1 in
let fac3 = fac_fun fac2 in
let fac4 = fac_fun fac3 in

(* fac4 computes the correct value of n! for n=0..3 *)

(* The Y combinator (for applicative-order evaluation strategy) *)
let fix =
  fun f ->
    (fun x ->
      f (fun n f y -> (x x) n f y))
      (fun x -> f (fun n f y -> (x x) n f y))
in

(* Define fac as fixpoint of fac_fun *)
let fac = fix fac_fun in

(* Convert a Church boolean to the built-in bool data type *)
let to_bool = fun b -> b true false in

(* Convert a Church numeral to the built-in int data type *)
let to_int = fun n -> n (fun x -> x + 1) 0 in

(* Compute 5! *)
to_int (fac five)
