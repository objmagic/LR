(* A GADT that captures Yacc production rule

   e.g. E : X Y Z { sem_act }
   
   this should have type (a -> b -> c -> d, d) syn
*)


(* Note: it's actually impossible to have other kinds of token, like int token *)
type eof

type _ token =
  | Char : char -> char token
  | Chars : char list -> char token
  | Eps : unit token
  | Eof : eof token

let compare_token : type a b. a token -> b token -> bool = fun l r ->
  match l, r with
  | Char cx, Char cy -> cx = cy
  | Chars clx, Chars cly -> clx = cly
  | Eps, Eps -> true
  | Eof, Eof -> true
  | _ -> false

type token_list =
  | TEmpty : token_list
  | TCons  : 'a token * token_list -> token_list

let rec compare_token_list : token_list -> token_list -> bool = fun l r ->
  match l, r with
  | TEmpty, TEmpty -> true
  | TCons (h1, t1), TCons (h2, t2) ->
    (compare_token h1 h2) && (compare_token_list t1 t2)
  | _, _ -> false

let token_list_length t =
  let rec loop t acc =
    match t with
    | TEmpty -> acc
    | TCons (_, tl) -> loop tl (acc + 1) in
  loop t 0

(* Define symbol and prod_rule as extensible types, so later we
   can redefine a constructor. Totally hack *)
type _ symbol = ..
type _ prod_rule = ..
  
type _ symbol +=
  | T  : 'a token -> 'a symbol
  | NT : 'a prod_rule list Lazy.t -> 'a symbol

type _ prod_rule +=
  | SemAct : 'a -> 'a prod_rule
  | Appl   : ('a -> 'b) prod_rule * 'a symbol -> 'b prod_rule

(* Type definition for syntax *)
type (_, _) syn =
  | Empty : ('a, 'a) syn
  | Cons  : 'c symbol * ('a, 'b) syn -> ('c -> 'a, 'b) syn

(* Polymorphic function that iterates each symbol in syntax list *)
type iter_syn = {iter : 'a. 'a symbol -> unit}

let rec iter_syntax : type a b. iter_syn -> (a, b) syn -> unit = fun iter s ->
  match s with
  | Empty -> ()
  | Cons (hd, tl) -> iter.iter hd; iter_syntax iter tl

(* Append symbol at the end of syntax list *)
let rec snoc : type a b c. (a, c -> b) syn -> c symbol -> (a, b) syn =
  fun l sym ->
    match l with
    | Empty -> Cons (sym, Empty)
    | Cons (sym', rhs) -> Cons (sym', snoc rhs sym)

(* 'a is the result type, 'b is the type of semantic function *)
type ('a, 'b) ss = {semantic : 'b; syntax : ('b, 'a) syn}

(* There is some problem with existential unpacking *)
type _ norm_prod_rule =
  | S : ('a, 'b) ss -> 'a norm_prod_rule

(* [module SRMap] is an heterogeneous association list of [norm_prod_rule list] *)
module SRMap = struct

  type _ acc = ..

  type (_, _) equality =
    | Refl : ('a, 'a) equality

  type 'a key = {
    k  : 'a prod_rule list;
    tag : 'a acc;
    eq  : 'b. 'b acc -> ('a, 'b) equality option
  }

  type 'a value = 'a norm_prod_rule list

  let fresh_key (type a) (w: a prod_rule list) : a key =
    let module M = struct type _ acc += T : a acc end in
    let eq : type b. b acc -> (a, b) equality option =
      function M.T -> Some Refl | _ -> None in
    {k = w; tag = M.T; eq}

  let gen rules =
    (fresh_key rules), rules

  type t =
    | SNil : t
    | SCons : 'a key * 'a value * t -> t

  let compare_keys : 'a key -> 'b key -> ('a, 'b) equality option = fun k1 k2 ->
    k1.eq k2.tag

  let rec find: type a. t -> a key -> a value option = fun l k ->
    match l with
    | SNil -> None
    | SCons (k', v, tl) ->
      match compare_keys k k' with
      | None -> find tl k
      | Some Refl -> Some v

  let rec add : type a. t -> a key -> a value -> t = fun l k v ->
    SCons (k, v, l)

  let empty = SNil

end

(* Redefine NT. Totally hack *)
type _ symbol +=
  | NT : ('a SRMap.key * 'a prod_rule list) Lazy.t -> 'a symbol

(* compare symbols *)
let compare_symbols : type a b. a symbol -> b symbol -> bool = fun s1 s2 ->
  match s1, s2 with
  | T t1 , T t2 -> compare_token t1 t2
  | T _ , NT _ -> false
  | NT _, T _ -> false
  | NT p1 , NT p2 -> begin
    let k1, _ = Lazy.force p1 and k2, _ = Lazy.force p2 in
    match SRMap.compare_keys k1 k2 with
    | Some _ -> true
    | None -> false
    end
  | _, _ -> false

(* split semantic action and syntax from an applicative structure *)
let rec split : type a. a prod_rule -> a norm_prod_rule = function
  | SemAct semantic -> S {semantic; syntax = Empty}
  | Appl (f, sym) ->
    let S {semantic; syntax} = split f in
    S {semantic; syntax = snoc syntax sym}
  | _ -> assert false

let normalize_symbol: type a. a symbol -> a norm_prod_rule list = function
  | T _ as t -> [S {semantic= (fun x -> x); syntax = Cons (t, Empty)}]
  | NT k_rules -> List.map split (snd (Lazy.force k_rules))
  | _ -> assert false

let normalize_rule_lists : type a. (a prod_rule list) -> (a norm_prod_rule list) = fun pl ->
  List.map split pl

let pure f = SemAct f
let (<*>) a b = Appl (a, b)

let exact c = T (Char c)
let exact_one_of cs = T (Chars cs)

let digit = exact_one_of ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9']


(* Grammar 4.55 from Aho's Dragon book *)
type s = SS of c * c
and c = C1 of char * c | C2 of char

let rec s = NT (lazy (SRMap.gen [
    (pure (fun c1 c2 -> SS (c1, c2)) <*> c <*> c)]))
and c = NT (lazy (SRMap.gen [
    (pure (fun ch c -> C1 (ch, c)) <*> exact 'c' <*> c);
    (pure (fun c -> C2 c) <*> exact 'd')]))

(* Grammar 4.1 from Aho's Dragon book *)
type e = E1 of e * t | E2 of t
and t = T1 of t * f | T2 of f
and f = F1 of e | F2 of int

let rec e = NT (lazy (SRMap.gen ([
  (pure (fun e t -> E1 (e, t)) <*> e <*> t);
  (pure (fun t -> E2 t) <*> t)])))

and t = NT (lazy (SRMap.gen([
  (pure (fun t f -> T1 (t, f)) <*> t <*> f);
  (pure (fun f -> T2 f) <*> f)])))

and f = NT (lazy (SRMap.gen ([
  (pure (fun _ e _ -> F1 e) <*> exact '(' <*> e <*> exact ')');
  (pure (fun d -> F2 (int_of_char d)) <*> digit)])))

let build_srmap s =
  let srmap = ref (SRMap.empty) in
  let rec dfs : type a. a symbol -> unit = fun s ->
    match s with
    | T _ -> ()
    | NT kr as nt -> begin
      let k = fst (Lazy.force kr) in
      match SRMap.find !srmap k with
      | Some _ -> ()
      | None -> begin
        let npr = normalize_symbol nt in
        srmap := SRMap.add !srmap k npr;
        List.iter (fun (S s) -> iter_syntax {iter = dfs} s.syntax) npr
        end
      end
    | _ -> () in
  dfs s;
  !srmap

type (_, _) item =
  | Item : 'c SRMap.key *
           ('a, 'b) syn * ('b, 'c) syn * token_list -> ('a, 'c) item

let rec compare_syns : type a b c d. (a, b) syn -> (c, d) syn -> bool = fun s1 s2 ->
  match s1, s2 with
  | Empty, Empty -> true
  | Cons (_, _), Empty -> false
  | Empty, Cons (_, _) -> false
  | Cons (hdx, tlx), Cons (hdy, tly) ->
    compare_symbols hdx hdy && compare_syns tlx tly

let compare_items : type a b c d. (a, b) item -> (c, d) item -> bool = fun s1 s2 ->
  match s1, s2 with
  | Item (k1, sx1, sy1, tlist1), Item (k2, sx2, sy2, tlist2) ->
    match SRMap.compare_keys k1 k2 with
    | None -> false
    | Some _ ->
      compare_syns sx1 sy1 && compare_syns sx2 sy2 && compare_token_list tlist1 tlist2

let srmap = build_srmap s

let augment : type a b. a symbol -> SRMap.t -> SRMap.t * (a -> a, a) item = fun s env ->
  match s with
  | NT n as nt -> begin
    let k = fst (Lazy.force n) in
    match SRMap.find env k with
    | None -> failwith "unknown error"
    | Some r ->
      let hd_syn = Empty and tl_syn = Cons (nt, Empty) in
      let augmented_rules = [pure (fun x -> x) <*> nt] in
      let normed_rules = List.map split augmented_rules in
      let key = SRMap.fresh_key augmented_rules in
      let new_env = SRMap.add env key normed_rules in
      new_env, Item (key, hd_syn, tl_syn, TEmpty)
    end
  | _ -> failwith "unknown"

let new_env, augmented_start_symbol = augment s srmap

let shift_dot : type a b. (a, b) item -> (a, b) item = fun item ->
  match item with
  | Item (k, alpha, Empty, token_list) -> failwith "Impossible to move dot"
  | Item (k, alpha, Cons (hd, tl), token_list) ->
    Item (k, (snoc alpha hd), tl, token_list)

(* Problem:
   S -> C {$1}
   C -> cd {$1}
   C -> efg {$1}
   
   given "S : .C", we would like to compute closure.
   what should be the return type of the function?
 
  we should return two items of different types.
   (char -> char -> char, char) item
   (char -> char -> char -> char, char) item

  Is there a good workaround of this problem?

*)

type 'a cont = {
  k: 'b 'c. ('b, 'c) item -> 'a;
}

let rule_to_item : type a b. a norm_prod_rule -> a SRMap.key -> token_list -> b cont -> b = fun r k tl cont ->
  match r with
  | S ss ->
    let syn = ss.syntax in
    cont.k (Item (k, Empty, syn, tl))

let one_step_close : type a b c. (a, b) item -> SRMap.t -> c cont -> c list = fun item env cont ->
  match item with
  | Item (k, alpha, Empty, token_list) -> []
  | Item (k, alpha, Cons(hd, tl), token_list) -> begin
    match hd with
    | T _ -> []
    | NT pair -> begin
      let k, _ = Lazy.force pair in
      match SRMap.find env k with
      | None -> failwith "Unprocessed non-terminal"
      | Some rules -> List.map (fun r -> rule_to_item r k token_list cont) rules
      end
    | _ -> assert false
    end
