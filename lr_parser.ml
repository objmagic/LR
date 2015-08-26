(* First, a GADT definition to capture Yacc production rule

   e.g. E : X Y Z { sem_act }
   this should have type (a -> b -> c -> d, d) syn
*)

(* it's actually impossible to have other kinds of token, like int token *)

module type HMap = sig
  type t
  type 'a key
  type 'a value
  type 'a witness
  val fresh_key : 'a witness -> 'a key
  val empty : t
  val add : t -> 'a key -> 'a value -> t
  val find : t -> 'a key -> 'a value option
  val size : t -> int
  val combine : t -> t -> t
end

module MakeHMap (V: sig type _ v and _ w end) :
  HMap with type 'a value := 'a V.v
        and type 'a witness := 'a V.w = struct

  type _ acc = ..

  type (_, _) equality =
    | Refl : ('a, 'a) equality

  type 'a key = {
    k: 'a acc;
    eq : 'b. 'b acc -> ('a, 'b) equality option;
  }

  type 'a value = 'a V.v
  
  type 'a witness = 'a V.w

  type t =
    | Nil : t
    | Cons : 'a key * 'a value * t -> t

  let fresh_key (type a) (w: a witness) =
    let module M = struct type _ acc += T : a acc end in
    let eq : type b. b acc -> (a, b) equality option =
      function M.T -> Some Refl | _ -> None in
    {k = M.T; eq}

  let empty = Nil

  let add t k v =
    Cons (k, v, t)

  let rec find : type a. t -> a key -> a value option =
    fun t k ->
      match t with
      | Nil -> None
      | Cons ({k = k'}, v, rest) ->
        match k.eq k' with
        | Some Refl -> Some v
        | None -> find rest k

  let size t =
    let rec loop t acc =
      match t with
      | Nil -> acc
      | Cons (_, _, res) -> loop res (acc + 1) in
    loop t 0

  let rec combine : t -> t -> t = fun x y ->
    match x with
    | Nil -> y
    | Cons (k, v, tl) -> Cons (k, v, (combine tl y))

end

type eof

type _ token =
  | Char : char -> char token
  | Chars : char list -> char token
  | Eps : unit token
  | Eof : eof token

type tlist =
  | TEmpty : tlist
  | TCons  : 'a token * tlist -> tlist

let tllen t =
  let rec loop t acc =
    match t with
    | TEmpty -> acc
    | TCons (_, tl) -> loop tl (acc + 1) in
  loop t 0

(* some hack ... *)
type _ symbol = ..
type _ prod_rule = ..
  
type _ symbol +=
  | T  : 'a token -> 'a symbol
  | NT : 'a prod_rule list Lazy.t -> 'a symbol

type _ prod_rule +=
  | SemAct : 'a -> 'a prod_rule
  | Appl   : ('a -> 'b) prod_rule * 'a symbol -> 'b prod_rule

type (_, _) syn =
  | Empty : ('a, 'a) syn
  | Cons  : 'c symbol * ('a, 'b) syn -> ('c -> 'a, 'b) syn

type iter_syn = {iter : 'a. 'a symbol -> unit}

let rec iter_syntax : type a b. iter_syn -> (a, b) syn -> unit = fun iter s ->
  match s with
  | Empty -> ()
  | Cons (hd, tl) -> iter.iter hd; iter_syntax iter tl

(* By Jeremy ... *)
let rec snoc : type a b c. (a, c -> b) syn -> c symbol -> (a, b) syn =
  fun l sym ->
    match l with
    | Empty -> Cons (sym, Empty)
    | Cons (sym', rhs) -> Cons (sym', snoc rhs sym)

type ('a, 'b) ss = {semantic : 'b; syntax : ('b, 'a) syn}

type _ norm_prod_rule =
  | S : ('a, 'b) ss -> 'a norm_prod_rule

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
    | Nil : t
    | Cons : 'a key * 'a value * t -> t

  let compare_keys : 'a key -> 'b key -> ('a, 'b) equality option = fun k1 k2 ->
    k1.eq k2.tag


  let rec find: type a. t -> a key -> a value option = fun l k ->
    match l with
    | Nil -> None
    | Cons (k', v, tl) ->
      match k.eq k'.tag with
      | None -> find tl k
      | Some Refl -> Some v

  let rec add : type a. t -> a key -> a value -> t = fun l k v ->
    Cons (k, v, l)

  let empty = Nil

end

(* Redefine NT. totally hack *)
type _ symbol +=
  | NT : ('a SRMap.key * 'a prod_rule list) Lazy.t -> 'a symbol

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

(* maybe we still need heterogeneous associative map to avold cyclic traversal *)
let pure f = SemAct f
let (<*>) a b = Appl (a, b)

(* q: still want to use <*> to represent either? *)
let exact c = T (Char c)
let exact_one_of cs = T (Chars cs)

let digit = exact_one_of ['0';'1';'2';'3';'4';'5';'6';'7';'8';'9']

(* Grammar 4.1 from Aho's Dragon book *)
type e = E1 of e * t | E2 of t
and t = T1 of t * f | T2 of f
and f = F1 of e | F2 of int

(* Grammar 4.55 from Aho's Dragon book *)
type s = SS of c * c
and c = C1 of char * c | C2 of char

let rec s = NT (lazy (SRMap.gen [
    (pure (fun c1 c2 -> SS (c1, c2)) <*> c <*> c)]))
and c = NT (lazy (SRMap.gen [
    (pure (fun ch c -> C1 (ch, c)) <*> exact 'c' <*> c);
    (pure (fun c -> C2 c) <*> exact 'd')]))

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

type 'a item = {
  key       : 'a SRMap.key;
  prod_rule : 'a norm_prod_rule;
  lookahead : tlist;
  dot       : int; (* better representation? *)
}

module ItemSet = struct

  type t =
    | Nil : t
    | Cons : 'a item * t -> t

  type iteritem = {iter : 'a. 'a item -> unit}

  let rec iter : iteritem -> t -> unit = fun i t ->
    match t with
    | Nil -> ()
    | Cons (hd, tl) -> i.iter hd; iter i tl
    
  let compare_item : 'a item -> 'b item -> bool = fun a b ->
    match (SRMap.compare_keys a.key b.key) with
    | Some _ when a.dot = b.dot && a.lookahead = b.lookahead -> true
    | _ -> false

  let rec mem : 'a item -> t -> bool = fun item t ->
    match t with
    | Nil -> false
    | Cons (item', rest) ->
      if compare_item item item then true else mem item rest

  let empty = Nil

  let add : 'a item -> t -> t = fun i t -> Cons (i, t)

  let augment_start : type a. a symbol -> t = function
    | NT _ as nt ->
      let aug_rule = pure (fun x -> x) <*> nt in
      let key = SRMap.fresh_key [aug_rule] in
      let item = {
        key;
        prod_rule = split aug_rule;
        lookahead = TCons (Eof, TEmpty);
        dot = 0;
      } in add item empty
    | _ -> assert false

end
