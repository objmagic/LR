(* A GADT that captures Yacc production rule

   e.g. E : X Y Z { sem_act }

   this should have type (a -> b -> c -> d, d) syn
*)

module O = Ordering

module type UDT = sig

  type t
  type eof
  val compare : t -> t -> int
  val to_string :t -> string
  val eof_to_string : string

end

module Token (UserDefinedToken : UDT) = struct

  module UDT = UserDefinedToken

  type _ token =
    | Tk : UDT.t -> UDT.t token
    | Eps : unit token
    | Eof : UDT.eof token

  and tbox = TokBox : 'a token -> tbox

  let tok t = Tk t

  let compare_token : type a b. a token -> b token -> (a, b) O.ordering =
    fun l r ->
      match l, r with
      | Tk t1, Tk t2 -> begin
        let c = UDT.compare t1 t2 in
        if c = 0 then O.EQ else (if c < 0 then O.LT else O.GT)
        end
      | Eps, Eps -> O.EQ
      | Eof, Eof -> O.EQ
      | _, _ -> begin
          match () with
          | () when TokBox l < TokBox r -> O.LT
          | () -> O.GT
        end

  module TokenOrder = struct
    type 'a t = 'a token

    let compare = compare_token
  end

  include Hset.Make(TokenOrder)

  let token_to_string : type a. a token -> string = fun t ->
    match t with
    | Tk t -> UDT.to_string t
    | Eps -> "Epsilon"
    | Eof -> UDT.eof_to_string

  let token_list_to_string tl =
    let f = {fold = fun t acc -> token_to_string t :: acc} in
    let strs = List.rev (fold f tl []) in
    String.concat " " strs

end

module CharToken = struct
  type t = char
  type eof
  let compare c1 c2 = Char.compare c1 c2
  let to_string t = String.make 1 t
  let eof_to_string = "EOF"
end

module Tok = Token(CharToken)

(* Define symbol and prod_rule as extensible types, so later we
   can redefine a constructor. Totally hack *)
type _ symbol = ..
type _ prod_rule = ..

type _ symbol +=
  | T  : 'a Tok.token -> 'a symbol                 (* Terminal *)
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
    cmp : 'b. 'b acc -> ('a, 'b) O.ordering;
  }

  type 'a value = 'a norm_prod_rule list

  let stamp =
    let i = ref 0 in
    fun () -> incr i; Printf.sprintf "T%d" !i

  let fresh_key (type a) (w: a prod_rule list) : a key =
    let module M = struct type _ acc += T : a acc end in
    let eq : type b. b acc -> (a, b) equality option =
      function M.T -> Some Refl | _ -> None in
    let cmp : type b. b acc -> (a, b) O.ordering = function
       M.T -> O.EQ
     | v when Boxed_acc M.T < Boxed_acc v -> O.LT
     | _ -> O.GT
    in
    {k = w; tag = M.T; stamp = stamp (); eq; cmp}

  let gen rules =
    (fresh_key rules), rules

  let compare_keys : 'a 'b. 'a key -> 'b key -> ('a, 'b) O.ordering =
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

type sbox = SymBox : 'a symbol -> sbox

let symbol_to_string : type a. a symbol -> string = fun s ->
  match s with
  | T token -> Tok.token_to_string token
  | NT (lazy ({SRMap.stamp}, _)) -> stamp
  | _ -> assert false

(* very costly, should use hashtbl, maybe GADT hashtbl? *)
(* compare symbols *)
let compare_symbols : type a b. a symbol -> b symbol -> (a, b) O.ordering = fun s1 s2 ->
  match s1, s2 with
  | T t1 , T t2 -> Tok.compare_token t1 t2
  | NT (lazy (k1,_)), NT (lazy (k2, _)) -> SRMap.compare_keys k1 k2
  | T _, NT _ -> O.LT
  | _ -> O.GT

(* split semantic action and syntax from an applicative structure *)
let rec split : type a. a prod_rule -> a norm_prod_rule = function
  | SemAct semantic -> S {semantic; syntax = SNil}
  | Appl (f, sym) ->
    let S {semantic; syntax} = split f in
    S {semantic; syntax = snoc syntax sym}
  | _ -> assert false

let normalize_symbol: type a. a symbol -> a norm_prod_rule list = function
  | T _ as t -> [S {semantic= (fun x -> x); syntax = SCons (t, SNil)}]
  | NT (lazy (_, k_rules)) -> List.map split k_rules
  | _ -> assert false

let normalize_rule_lists : type a. (a prod_rule list) -> (a norm_prod_rule list) = fun pl ->
  List.map split pl

let pure f = SemAct f
let (<*>) a b = Appl (a, b)

let exact c = T (Tok.tok c)

let build_srmap s =
  let srmap = ref (SRMap.empty) in
  let rec dfs : type a. a symbol -> unit = fun s ->
    match s with
    | T _ -> ()
    | NT (lazy (k, _)) as nt -> begin
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

let syn_to_string : type a b. (a, b) syn -> string = fun s ->
  let buf = Buffer.create 20 in
  let f s =
    Buffer.add_string buf (symbol_to_string s); Buffer.add_string buf " " in
  let iter = {iter = f} in
  iter_syntax iter s;
  Buffer.contents buf

module ItemSet = struct

  type (_, _) item =
    | Item : 'c SRMap.key *   (* Key associated with item *)
             ('a, 'b) syn *   (* symbols before dot *)
             ('b, 'c) syn *   (* symbols after dot *)
             Tok.t       (* look ahead *)
             -> ('a, 'c) item

  let item_to_string : type a b. (a, b) item -> string = fun item ->
    match item with
    | Item (k, fst, snd, tl) ->
      Printf.sprintf "%s -> %s . %s [%s]"
      (k.SRMap.stamp)
      (syn_to_string fst)
      (syn_to_string snd)
      (if Tok.is_empty tl then "$" else Tok.token_list_to_string tl)


  let rec compare_syns :
    type a b c d. (a, b) syn -> (c, d) syn -> (_, _) O.ordering = fun s1 s2 ->
      match s1, s2 with
      | SNil, SNil -> O.EQ
      | SCons (_, _), SNil -> O.GT
      | SNil, SCons (_, _) -> O.LT
      | SCons (hdx, tlx), SCons (hdy, tly) ->
        match compare_symbols hdx hdy, compare_syns tlx tly with
        | O.EQ, O.EQ -> O.EQ
        | O.EQ, O.GT -> O.GT
        | O.EQ, O.LT -> O.LT
        | O.GT, _ -> O.GT
        | O.LT, _ -> O.LT

  let compare_items :
    type a b c d. (a, b) item -> (c, d) item -> (_, _) O.ordering = fun s1 s2 ->
    match s1, s2 with
    | Item (k1, sx1, sy1, t1), Item (k2, sx2, sy2, t2) ->
      match SRMap.compare_keys k1 k2 with
      | O.EQ -> begin
        match compare_syns sx1 sy1, compare_syns sx2 sy2 with
        | O.EQ, O.EQ -> begin
          let c = Tok.compare t1 t2 in
          if c = 0 then O.EQ else (if c < 0 then O.LT else O.GT)
          end
        | O.EQ, O.LT -> O.LT
        | O.EQ, O.GT -> O.GT
        | O.LT, _ -> O.LT
        | O.GT, _ -> O.GT
        end
      | O.LT -> O.LT (* I have to explicitly write this out ?? *)
      | O.GT -> O.GT

  module ItemOrder = struct
    type ('a, 'b) t = ('a, 'b) item

    let compare : type a b c d. (a, b) t -> (c, d) t -> (_, _) O.ordering =
      compare_items
  end

  include Hset2.Make(ItemOrder)

  let union_all ss =
    List.fold_left union empty ss

  let to_string s =
    let buf = Buffer.create 20 in
    let f item =
      Buffer.add_string buf (item_to_string item);
      Buffer.add_string buf "\n" in
    let it = {iter=f} in
    iter it s;
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
        new_env, singleton (Item (key, hd_syn, tl_syn, Tok.empty))
      end
    | _ -> invalid_arg "ItemSet.argument_start: Invalid symbol"

  let shift_dot : type a b. (a, b) item -> (a, b) item option = fun item ->
    match item with
    | Item (k, alpha, SNil, token_list) -> None
    | Item (k, alpha, SCons (hd, tl), token_list) ->
      Some (Item (k, (snoc alpha hd), tl, token_list))

  let shift_dot_exn : type a b. (a, b) item -> (a, b) item = fun item ->
    match item with
    | Item (k, alpha, SNil, token_list) -> invalid_arg "ItemSet.shift_dot_exn"
    | Item (k, alpha, SCons (hd, tl), token_list) ->
      Item (k, (snoc alpha hd), tl, token_list)

  let rule_to_itemset :
    type a b. a norm_prod_rule -> a SRMap.key -> Tok.t -> t =
    fun r k tl ->
      match r with
      | S ss ->
        let syn = ss.syntax in
        singleton (Item (k, SNil, syn, tl))

  let first_set : type a b. (a, b) syn -> SRMap.t -> Tok.t = fun s env ->
    let rec loop : type a b. (a, b) syn -> Tok.t = fun s ->
      match s with
      | SNil -> Tok.empty
      | SCons (hd, tl) -> begin
        match hd with
        | T t -> begin
          let cont : type a. a Tok.token -> Tok.t = fun t ->
            match t with
            | Tok.Eps -> loop tl
            | _ -> Tok.add t Tok.empty in
          cont t
          end
        | NT p -> begin
          let k, _ = Lazy.force p in
          match SRMap.find env k with
          | Some rules ->
            let fold_f acc r =
              match r with
              | S ss -> Tok.union acc (loop ss.syntax) in
            List.fold_left fold_f Tok.empty rules
          | None -> Tok.empty
          end
        | _ -> assert false
        end in
    loop s

  let close_item : type a b c. (a, b) item -> SRMap.t -> t = fun item env ->
    let loop : type a b c. (a, b) item -> SRMap.t -> Tok.t -> t = fun item env l ->
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
              let t = first_set tl env in
              if Tok.is_empty t then token_list else t in
            let items = List.map (fun r -> rule_to_itemset r k first) rules in
            union_all items
            end
          end
        | _ -> assert false
        end in
    match item with
    | Item (_, _, _, token_list) -> loop item env token_list

  let close_items set env =
    let f = {fold = fun item acc -> union acc (close_item item env)} in
    fold f set empty

  let closure : t -> SRMap.t -> t = fun set env ->
    let rec loop set acc =
      if is_empty set then acc else begin
        loop (close_items set env) (union set acc) end in
    loop (close_items set env) set
end

module Automata = struct

  type state = ..  (* hack *)

  module TransOrder = struct
    type 'a t = 'a symbol
    type 'a value = state
    let compare = compare_symbols
  end

  module Transitions = Hmap.Make(TransOrder)

  type s = {
    items : ItemSet.t;
    mutable trans : Transitions.t
  }

  type state += State of s

  module StateOrder = struct
    type t = state
    let compare = fun s1 s2 ->
      match s1, s2 with
      | State s1, State s2 -> ItemSet.compare s1.items s2.items
      | _, _ -> assert false
  end

  include Set.Make(StateOrder)

  let exists_items items' t = exists (fun k ->
      match k with
      | State s -> ItemSet.compare items' s.items = 0
      | _ -> assert false)

  let rec add_item_to_transet :
    's symbol -> ('a, 'b) ItemSet.item -> Transitions.t -> Transitions.t =
    fun sym item ts ->
      match Transitions.find sym ts with
      | Some (State state) -> begin
          let new_items = ItemSet.add item state.items in
          Transitions.add sym (State {state with items = new_items}) ts
        end
      | None -> begin
        let state = State {
            items = ItemSet.add item ItemSet.empty;
            trans = Transitions.empty;} in
        Transitions.add sym state ts
        end
  
  let build_transet : ItemSet.t -> Transitions.t = fun its ->
    let fold :
      type a b. (a, b) ItemSet.item -> Transitions.t -> Transitions.t =
      fun it l ->
        match it with
        | ItemSet.Item (_, _, SCons (s, _), _) ->
          add_item_to_transet s (ItemSet.shift_dot_exn it) l
        | _ -> l in
    ItemSet.fold {ItemSet.fold} its Transitions.empty

  let rec aug_transet : Transitions.t -> SRMap.t -> t -> Transitions.t =
    fun l env am ->
      let fold sym state acc =
        match state with
        | State {items; trans} -> begin
            let new_items = ItemSet.closure items env in
            let phantom_set =
              State {items = new_items; trans = Transitions.empty} in
            try
              let exist_set = find phantom_set am in
              Transitions.add sym exist_set acc
            with Not_found ->
              let new_state = State {items = new_items; trans;} in
              Transitions.add sym new_state acc
          end
        | _ -> assert false in
      Transitions.fold {Transitions.fold} l Transitions.empty
      (* The above line looks really weird, isn't it? *)

  module ItemSetSet = Set.Make(struct
      type t = ItemSet.t
      let compare = ItemSet.compare
    end)

  let build_automata : ItemSet.t -> SRMap.t -> state * t = fun is env ->
    let states = ref empty in
    let visited = ref ItemSetSet.empty in
    let rec visit s () =
      match s with
      | State state -> begin
          let {items; trans} = state in
          if ItemSetSet.mem items !visited then () else begin
            visited := ItemSetSet.add items !visited;
            states := add s !states;
            let new_trans = aug_transet (build_transet items) env !states in
            state.trans <- new_trans;
            let iter : type a. a symbol -> state -> unit = fun _ s' ->
              visit s' () in
            Transitions.iter {Transitions.iter} new_trans
          end
        end
      | _ -> assert false in
    let s0 = State {items = is; trans = Transitions.empty} in
    visit s0 ();
    s0, !states

  (*
  let automata_to_string state =
    let htb : (int, int) Hashtbl.t = Hashtbl.create 64 in
    let hadd, hlookup =
      let i = ref 0 in
      (fun is -> incr i; Hashtbl.add htb (Hashtbl.hash is) !i),
      (fun is -> try Some (Hashtbl.find htb (Hashtbl.hash is)) with _ -> None) in
    let buf = Buffer.create 64 in
    let rec visit s () =
      let {items; trans} = s in
      match hlookup items with
      | Some _ -> ()
      | None -> begin
          hadd items;
          itertl {iter = fun (Trans (_, st)) -> visit st ()} trans
        end in
    visit state ();
    let htb1 : (int, bool) Hashtbl.t = Hashtbl.create 64 in
    let rec visit s () =
      let {items; trans} = s in
      let k = Hashtbl.hash items in
      if Hashtbl.mem htb1 k then () else begin
        Hashtbl.add htb1 k true;
        Buffer.add_string buf (Printf.sprintf "State S%d:\n" (Hashtbl.find htb k));
        Buffer.add_string buf (ItemSet.to_string items);
        let iter = (fun (Trans (sym, {items})) ->
          Buffer.add_string buf (Printf.sprintf "from: %s to " (symbol_to_string sym));
          Buffer.add_string buf (Printf.sprintf "S%d \n" (Hashtbl.find htb (Hashtbl.hash items)))) in
        itertl {iter} trans;
        Buffer.add_string buf "---------\n";
        let iter = fun (Trans (_, st)) -> visit st () in
        itertl {iter} trans
      end in
    visit state ();
    Buffer.contents buf
  *)

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

  let s0, states = Automata.build_automata s_first env

(*
  let ams = Automata.automata_to_string s0

  let dump () = print_endline ams
*)

end


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
