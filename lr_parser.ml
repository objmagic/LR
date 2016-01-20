(* A GADT that captures Yacc production rule

   e.g. E : X Y Z { sem_act }

   this should have type (a -> b -> c -> d, d) syn
*)

(* Note: it's actually impossible to have other kinds of token, like int token *)

module type UDT = sig

  type t
  type eof
  val equal : t -> t -> bool
  val to_string :t -> string
  val eof_to_string : string

end

module Token (UserDefinedToken : UDT) = struct

  module UDT = UserDefinedToken

  type _ token =
    | Tk : UDT.t -> UDT.t token
    | Eps : unit token
    | Eof : UDT.eof token

  let tok t = Tk t

  let equal_token : type a b. a token -> b token -> bool = fun l r ->
    match l, r with
    | Tk t1, Tk t2 -> UDT.equal t1 t2
    | Eps, Eps -> true
    | Eof, Eof -> true
    | _ -> false

  type token_list =
    | TNil : token_list
    | TCons  : 'a token * token_list -> token_list

  let rec exist : type a. a token -> token_list -> bool = fun t l ->
    match l with
    | TNil -> false
    | TCons (hd, tl) ->
      if equal_token t hd then true else exist t tl

  let rec equal_token_list : token_list -> token_list -> bool = fun l r ->
    match l, r with
    | TNil, TNil -> true
    | TCons (h1, t1), TCons (h2, t2) ->
      (equal_token h1 h2) && (equal_token_list t1 t2)
    | _, _ -> false

  (* O(n^2) *)
  let combine_token_list : token_list -> token_list -> token_list = fun t1 t2 ->
    let rec non_exist l acc =
      match l with
      | TNil -> acc
      | TCons (hd, tl) -> if exist hd t2 then acc else non_exist tl (TCons (hd, acc)) in
    let rec combine t1 t2 =
      match t1 with
      | TNil -> t2
      | TCons (hd, tl) -> TCons (hd, (combine tl t2)) in
    combine (non_exist t1 TNil) t2

  type iter_tk = {iter: 'a. 'a token -> unit}

  type 'a fold_tk = {fold: 'b. 'b token -> 'a -> 'a}

  let rec iter_token_list l iter =
    match l with
    | TNil -> ()
    | TCons (hd, tl) -> iter.iter hd; iter_token_list tl iter

  let rec fold_token_list l fold acc =
    match l with
    | TNil -> acc
    | TCons (hd, tl) -> fold_token_list tl fold (fold.fold hd acc)

  let token_list_length t =
    let f = {fold = fun _ acc -> 1 + acc} in
    fold_token_list t f 0

  let token_to_string : type a. a token -> string = fun t ->
    match t with
    | Tk t -> UDT.to_string t
    | Eps -> "Epsilon"
    | Eof -> UDT.eof_to_string

  let token_list_to_string tl =
    let f = {fold = fun t acc -> token_to_string t :: acc} in
    let strs = List.rev (fold_token_list tl f []) in
    String.concat " " strs

end

module CharToken = struct
  type t = char
  type eof
  let equal c1 c2 = Char.compare c1 c2 = 0
  let to_string t = String.make 1 t
  let eof_to_string = "EOF"
end

include Token(CharToken)

(* Define symbol and prod_rule as extensible types, so later we
   can redefine a constructor. Totally hack *)
type _ symbol = ..
type _ prod_rule = ..

type _ symbol +=
  | T  : 'a token -> 'a symbol                 (* Terminal *)
  | NT : 'a prod_rule list Lazy.t -> 'a symbol (* Non-terminal *)

(* production rule *)
type _ prod_rule +=
  | SemAct : 'a -> 'a prod_rule
  | Appl   : ('a -> 'b) prod_rule * 'a symbol -> 'b prod_rule

(* syntax *)
type (_, _) syn =
  | SNil : ('a, 'a) syn
  | SCons  : 'c symbol * ('a, 'b) syn -> ('c -> 'a, 'b) syn

(* iterates each symbol in symbol list *)
type iter_syn = {iter : 'a. 'a symbol -> unit}

let rec iter_syntax : type a b. iter_syn -> (a, b) syn -> unit = fun iter s ->
  match s with
  | SNil -> ()
  | SCons (hd, tl) -> iter.iter hd; iter_syntax iter tl

(* Append symbol at the end of syntax list *)
let rec snoc : type a b c. (a, c -> b) syn -> c symbol -> (a, b) syn =
  fun l sym ->
    match l with
    | SNil -> SCons (sym, SNil)
    | SCons (sym', rhs) -> SCons (sym', snoc rhs sym)

(* 'a is the result type, 'b is the type of semantic function *)
type ('a, 'b) ss = {semantic : 'b; syntax : ('b, 'a) syn}

(* normalized Yacc rule *)
type _ norm_prod_rule =
  | S : ('a, 'b) ss -> 'a norm_prod_rule

(* [module SRMap] is an heterogeneous map of [norm_prod_rule list] *)
module SRMap = struct

  type _ acc = ..

  type boxed_acc = Boxed_acc : _ acc -> boxed_acc

  type (_, _) equality =
    | Refl : ('a, 'a) equality

  type 'a key = {
    k  : 'a prod_rule list;
    tag : 'a acc;
    stamp: string;
    eq  : 'b. 'b acc -> ('a, 'b) equality option;
    cmp : 'b. 'b acc -> ('a, 'b) Hmap.ordering;
  }

  type 'a value = 'a norm_prod_rule list

  let stamp =
    let i = ref 0 in
    fun () -> incr i; Printf.sprintf "T%d" !i

  let fresh_key (type a) (w: a prod_rule list) : a key =
    let module M = struct type _ acc += T : a acc end in
    let eq : type b. b acc -> (a, b) equality option =
      function M.T -> Some Refl | _ -> None in
    let cmp : type b. b acc -> (a, b) Hmap.ordering = function
       M.T -> Hmap.EQ
     | v when Boxed_acc M.T < Boxed_acc v -> Hmap.LT
     | _ -> Hmap.GT
    in
    {k = w; tag = M.T; stamp = stamp (); eq; cmp}

  let gen rules =
    (fresh_key rules), rules

  let compare_keys : 'a 'b. 'a key -> 'b key -> ('a, 'b) Hmap.ordering =
    fun {cmp} {tag} -> cmp tag

  (* mapping from ['a key] to ['a value] *)
  module KVMap = Hmap.Make
    (struct 
       type 'a t = 'a key
       type 'a value = 'a norm_prod_rule list
       let compare l r = compare_keys l r
     end)
  type t = KVMap.t

  let equal_keys : 'a key -> 'b key -> ('a, 'b) equality option = fun k1 k2 ->
    k1.eq k2.tag

  let find: type a. t -> a key -> a value option =
    fun map k -> KVMap.find k map

  let add : type a. t -> a key -> a value -> t =
    fun map k v -> KVMap.add k v map

  let empty = KVMap.empty
end

exception Unnormalized_rule

(* Redefine NT. Totally hack *)
type _ symbol +=
  | NT : ('a SRMap.key * 'a prod_rule list) Lazy.t -> 'a symbol

let symbol_to_string : type a. a symbol -> string = fun s ->
  match s with
  | T token -> token_to_string token
  | NT p ->
    let k, _ = Lazy.force p in
    k.SRMap.stamp
  | _ -> assert false

(* very costly, should use hashtbl, maybe GADT hashtbl? *)
(* compare symbols *)
let equal_symbols : type a b. a symbol -> b symbol -> bool = fun s1 s2 ->
  match s1, s2 with
  | T t1 , T t2 -> equal_token t1 t2
  | T _ , NT _ -> false
  | NT _, T _ -> false
  | NT p1 , NT p2 -> begin
    let k1, _ = Lazy.force p1 and k2, _ = Lazy.force p2 in
    match SRMap.equal_keys k1 k2 with
    | Some _ -> true
    | None -> false
    end
  | _, _ -> false

(* split semantic action and syntax from an applicative structure *)
let rec split : type a. a prod_rule -> a norm_prod_rule = function
  | SemAct semantic -> S {semantic; syntax = SNil}
  | Appl (f, sym) ->
    let S {semantic; syntax} = split f in
    S {semantic; syntax = snoc syntax sym}
  | _ -> assert false

let normalize_symbol: type a. a symbol -> a norm_prod_rule list = function
  | T _ as t -> [S {semantic= (fun x -> x); syntax = SCons (t, SNil)}]
  | NT k_rules -> List.map split (snd (Lazy.force k_rules))
  | _ -> assert false

let normalize_rule_lists : type a. (a prod_rule list) -> (a norm_prod_rule list) = fun pl ->
  List.map split pl

let pure f = SemAct f
let (<*>) a b = Appl (a, b)

let exact c = T (Tk c)

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
  | Item : 'c SRMap.key *   (* Key associated with item *)
           ('a, 'b) syn *   (* symbols before dot *)
           ('b, 'c) syn *   (* symbols after dot *)
           token_list       (* look ahead *)
           -> ('a, 'c) item


let syn_to_string : type a b. (a, b) syn -> string = fun s ->
  let buf = Buffer.create 20 in
  let f s =
    Buffer.add_string buf (symbol_to_string s); Buffer.add_string buf " " in
  let iter = {iter = f} in
  iter_syntax iter s;
  Buffer.contents buf

let item_to_string : type a b. (a, b) item -> string = fun item ->
  match item with
  | Item (k, fst, snd, tl) ->
    Printf.sprintf "%s -> %s . %s [%s]"
    (k.SRMap.stamp)
    (syn_to_string fst)
    (syn_to_string snd)
    (match tl with
    | TNil -> "$"
    | _ -> token_list_to_string tl)

let rec equal_syns : type a b c d. (a, b) syn -> (c, d) syn -> bool = fun s1 s2 ->
  match s1, s2 with
  | SNil, SNil -> true
  | SCons (_, _), SNil -> false
  | SNil, SCons (_, _) -> false
  | SCons (hdx, tlx), SCons (hdy, tly) ->
    equal_symbols hdx hdy && equal_syns tlx tly


let equal_items : type a b c d. (a, b) item -> (c, d) item -> bool = fun s1 s2 ->
  match s1, s2 with
  | Item (k1, sx1, sy1, tlist1), Item (k2, sx2, sy2, tlist2) ->
    match SRMap.equal_keys k1 k2 with
    | None -> false
    | Some _ ->
      equal_syns sx1 sy1 && equal_syns sx2 sy2 && equal_token_list tlist1 tlist2


(* Core LR(1) automata engine *)
module ItemSet = struct
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

    Answer: try using heterogeneous list to hide this problem.
  *)

  type t =
    | INil : t
    | ICons : ('a, 'b) item * t -> t

  let empty = INil

  let rec mem elt s =
    match s with
    | INil -> false
    | ICons (hd, tl) ->
      if equal_items elt hd then true else mem elt tl

  type iter_itemset = {iter : 'a 'b. ('a, 'b) item -> unit}

  type 'c fold_itemset = {fold: 'a 'b. ('a, 'b) item -> 'c -> 'c}

  let rec iter_is : t -> iter_itemset -> unit = fun s it ->
    match s with
    | INil -> ()
    | ICons (hd, tl) -> it.iter hd; iter_is tl it

  let rec fold_is : t -> 'c fold_itemset -> 'c -> 'c = fun s it acc ->
    match s with
    | INil -> acc
    | ICons (hd, tl) -> fold_is tl it (it.fold hd acc)

  let add elt s =
    if mem elt s then s else ICons (elt, s)

  let singleton elt = ICons (elt, INil)

  let union s1 s2 =
    let rec loop s1 acc =
      match s1 with
      | INil -> acc
      | ICons (hd, tl) -> loop tl (add hd acc) in
    loop s1 s2

  let union_all ss =
    List.fold_left union empty ss

  let rec rev_iter : iter_itemset -> t -> unit = fun it s ->
    match s with
    | INil -> ()
    | ICons (hd, tl) ->  rev_iter it tl; it.iter hd

  let to_string s =
    let buf = Buffer.create 20 in
    let f item =
      Buffer.add_string buf (item_to_string item);
      Buffer.add_string buf "\n" in
    let it = {iter=f} in
    rev_iter it s;
    Buffer.contents buf

  exception Unpreprocessed_non_terminal_symbol

  let augment_start : type a b. a symbol -> SRMap.t -> SRMap.t * t = fun s env ->
    match s with
    | NT n as nt -> begin
      let k = fst (Lazy.force n) in
      match SRMap.find env k with
      | None -> raise Unpreprocessed_non_terminal_symbol
      | Some r ->
        let hd_syn = SNil and tl_syn = SCons (nt, SNil) in
        let augmented_rules = [pure (fun x -> x) <*> nt] in
        let normed_rules = List.map split augmented_rules in
        let key = SRMap.fresh_key augmented_rules in
        let new_env = SRMap.add env key normed_rules in
        new_env, singleton (Item (key, hd_syn, tl_syn, TNil))
      end
    | _ -> failwith "Invalid symbol"

  let shift_dot : type a b. (a, b) item -> (a, b) item option = fun item ->
    match item with
    | Item (k, alpha, SNil, token_list) -> None
    | Item (k, alpha, SCons (hd, tl), token_list) ->
      Some (Item (k, (snoc alpha hd), tl, token_list))

  let shift_dot_exn : type a b. (a, b) item -> (a, b) item = fun item ->
    match item with
    | Item (k, alpha, SNil, token_list) -> assert false
    | Item (k, alpha, SCons (hd, tl), token_list) ->
      Item (k, (snoc alpha hd), tl, token_list)


  let rule_to_itemset : type a b. a norm_prod_rule -> a SRMap.key -> token_list -> t = fun r k tl ->
    match r with
    | S ss ->
      let syn = ss.syntax in
      singleton (Item (k, SNil, syn, tl))

  let first_set : type a b. (a, b) syn -> SRMap.t -> token_list = fun s env ->
    let rec loop : type a b. (a, b) syn -> token_list = fun s ->
      match s with
      | SNil -> TNil
      | SCons (hd, tl) -> begin
        match hd with
        | T t -> begin
          let cont : type a. a token -> token_list = fun t ->
            match t with
            | Eps -> loop tl
            | _ -> TCons (t, TNil) in
          cont t
          end
        | NT p -> begin
          let k, _ = Lazy.force p in
          match SRMap.find env k with
          | Some rules ->
            let fold_f acc r =
              match r with
              | S ss -> combine_token_list acc (loop ss.syntax) in
            List.fold_left fold_f TNil rules
          | None -> TNil
          end
        | _ -> assert false
        end in
    loop s

  let close_item : type a b c. (a, b) item -> SRMap.t -> t = fun item env ->
    let loop : type a b c. (a, b) item -> SRMap.t -> token_list -> t = fun item env l ->
      match item with
      | Item (_, _, SNil, _) -> empty
      | Item (k, _, SCons (hd, tl), token_list) -> begin
        match hd with
        | T _ -> empty
        | NT pair -> begin
          let k, _ = Lazy.force pair in
          match SRMap.find env k with
          | None -> raise Unpreprocessed_non_terminal_symbol
          | Some rules -> begin
            let first =
              match first_set tl env with
              | TNil -> token_list
              | _ as l -> l in
            let items = List.map (fun r -> rule_to_itemset r k first) rules in
            union_all items
            end
          end
        | _ -> assert false
        end in
    match item with
    | Item (_, _, _, token_list) -> loop item env token_list

  let close_items set env =
    let rec collect set acc =
      match set with
      | INil -> acc
      | ICons (hd, tl) -> collect tl (union acc (close_item hd env)) in
    collect set INil

  let closure : t -> SRMap.t -> t = fun set env ->
    let rec loop set acc =
      match set with
      | INil -> acc
      | _ as s -> loop (close_items s env) (union s acc) in
    loop (close_items set env) set

  type translist =
    | TNil : translist
    | TCons : 's symbol * t * translist -> translist

  let rec translist_to_string : translist -> string = fun l ->
    let buf = Buffer.create 64 in
    let rec loop = function
      | TNil -> ()
      | TCons (s, t, l) ->
        let ss = Printf.sprintf "From %s to:\n" (symbol_to_string s) in
        Buffer.add_string buf ss;
        Buffer.add_string buf (to_string t);
        Buffer.add_string buf "\n\n";
        loop l in
    loop l;
    Buffer.contents buf

  let rec add_item_to_translist : type a b. 's symbol -> (a, b) item -> translist -> translist =
    fun s item l ->
      match l with
      | TNil -> TCons (s, singleton item, TNil)
      | TCons (st, its, t) ->
        if equal_symbols s st then
          TCons (st, add item its, t)
        else
          TCons (st, its, add_item_to_translist s item t)

  let build_tranl : t -> translist = fun its ->
    let foldf : type a b. (a, b) item -> translist -> translist = fun it l ->
      match it with
      | Item (_, _, SCons (s, _), _) ->
        add_item_to_translist s (shift_dot_exn it) l
      | _ -> l in
    fold_is its {fold=foldf} TNil

  (* need memorization here! memo itemset!
     But, this could be diabolically inefficient *)
  let rec aug_transl : translist -> SRMap.t -> translist = fun l env ->
    match l with
    | TNil -> TNil
    | TCons (s, t, tl) ->
      TCons (s, closure t env, aug_transl tl env)

end

(*
   S -> C C
   C -> c C | d
*)

(* Grammar 4.55 from Aho's Dragon book *)
type s = SS of c * c
and c = C1 of char * c | C2 of char

let rec s = NT (lazy (SRMap.gen [
    (pure (fun c1 c2 -> SS (c1, c2)) <*> c <*> c)]))
and c = NT (lazy (SRMap.gen [
    (pure (fun ch c -> C1 (ch, c)) <*> exact 'c' <*> c);
    (pure (fun c -> C2 c) <*> exact 'd')]))

module Test = struct

  let env = build_srmap s

  (* [s_set] is kernel item set *)
  let env, s_set = ItemSet.augment_start s env

  let s_first = ItemSet.closure s_set env

  let get_first () =
    match s with
    | NT p -> begin
      let k, _ = Lazy.force p in
      match SRMap.find env k with
      | Some rules ->
        let fold_f acc r =
          match r with
          | S ss -> combine_token_list acc (ItemSet.first_set ss.syntax env) in
        List.fold_left fold_f TNil rules
      | None -> failwith "Unpreprocessed non-terminal symbols"
      end
    | _ -> assert false

  let see () = get_first () |> token_list_to_string

  let dump_s0 () = ItemSet.to_string s_first

  let s0_transl =
    ItemSet.aug_transl (ItemSet.build_tranl s_first) env

  let dump_trans () = ItemSet.translist_to_string s0_transl


end

let () = print_endline (Test.see ())

let () = print_endline (Test.dump_s0 ())

let () = print_endline (Test.dump_trans ())

(* Notes on challenges:

   Not to mention all ugliness brought by CSP and let-rec-and generation,
   what we are attempting to do constantly hits the limit of MetaOCaml or OCaml.

   1. reduce function
      say we have a function of form ``fun x y z -> x + y * z``.
      we would like to generate a function ``f`` of form:
     ``fun g x y z -> g (x + y * z)``

   2. pattern matching generation
      plan: using nested if-then-else

   3. performance problem
      our code is complete type-safe, so all comparison
      functions only tell you if two things are equal or not. This
      means we cannot have tree-like data structure to do O(logN) operation.
      e.g: ``equal_symbols`` can be very costly
      Thought: maybe using some hash?

   4. let-rec-and generation are almost solved by Jun Inoue and Oleg3.
      Actually, using Jeremy's current approach is not bad

*)
