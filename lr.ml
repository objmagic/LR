(* First, a GADT definition to capture Yacc production rule

   e.g. E : X Y Z { sem_act }
   this should have type (a -> b -> c -> d, d) syn
*)

type token =
  | Char of char
  | Chars of char list

type _ symbol =
  | T  : token -> 'a symbol
  | NT : 'a prod_rule list Lazy.t -> 'a symbol

and _ prod_rule =
  | SemAct : 'a -> 'a prod_rule
  | Appl   : ('a -> 'b) prod_rule * 'a symbol -> 'b prod_rule
  
type (_, _) syn =
  | Empty : ('a, 'a) syn
  | Cons  : 'c symbol * ('a, 'b) syn -> ('c -> 'a, 'b) syn

(* By Jeremy ... *)

let rec snoc : type a b c. (a, c -> b) syn -> c symbol -> (a, b) syn =
  fun l sym ->
    match l with
    | Empty -> Cons (sym, Empty)
    | Cons (sym', rhs) -> Cons (sym', snoc rhs sym)

type ('a, 'b) ss = {semantic : 'b; syntax : ('b, 'a) syn}

type _ norm_prod_rule  =
  | S : ('a, 'b) ss -> 'a norm_prod_rule

let rec split : type a. a prod_rule -> a norm_prod_rule = function
  | SemAct semantic -> S {semantic; syntax = Empty}
  | Appl (f, sym) ->
    let S {semantic; syntax} = split f in
    S {semantic; syntax = snoc syntax sym}

let normalize: type a. a symbol -> a norm_prod_rule list = function
  | T _ as t -> [S {semantic= (fun x -> x); syntax = Cons (t, Empty)}]
  | NT rules -> List.map split (Lazy.force rules)

type first = token list
type follow = token list
(* maybe we still need heterogeneous map to avold cyclic traversal *)

let pure f = SemAct f
let (<*>) a b = Appl (a, b)

(* q: still want to use <*> to represent either? *)

let exact c = T (Char c)
let exact_one_of cs = T (Chars cs)

(* Grammar 4.1 from Aho's Dragon book *)
type e = E1 of e * t | E2 of t
and t = T1 of t * f | T2 of f
and f = F1 of e | F2 of int

let digit = exact_one_of ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9']

let rec e = NT (lazy ([
  (pure (fun e t -> E1 (e, t)) <*> e <*> t);
  (pure (fun t -> E2 t) <*> t)]))
and t = NT (lazy ([
  (pure (fun t f -> T1 (t, f)) <*> t <*> f);
  (pure (fun f -> T2 f) <*> f)]))
and f = NT (lazy ([
  (pure (fun _ e _ -> F1 e) <*> exact '(' <*> e <*> exact ')');
  (pure (fun d -> F2 (int_of_char d)) <*> digit)]))
