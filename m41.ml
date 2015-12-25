(* Aho 4.1 *)

type token =
  KPlus | KStar | KLeft | KRight | KEnd | KInt of int | EOF

let peek = List.hd and rest = List.tl

module GADT = struct

  type empty = SEmpty
  (* stack *)
  type 'a cP = SP : 'a * 'a state       -> 'a cP (* Plus *)
  and  'a cS = SS : 'a * 'a state       -> 'a cS (* Star *)
  and  'a cL = SL : 'a * 'a state       -> 'a cL (* Left *)
  and  'a cR = SR : 'a * 'a state       -> 'a cR (* Right *)
  (* last field is semantic value *)
  and  'a cI = SI : 'a * 'a state * int -> 'a cI (* Int *)
  and  'a cE = SE : 'a * 'a state * int -> 'a cE (* Expression *)
  and  'a cT = ST : 'a * 'a state * int -> 'a cT (* Term *)
  and  'a cF = SF : 'a * 'a state * int -> 'a cF (* Factor *)

  (* States in action/goto table *)
  and _ state =
    | S0  : empty state
    | S1  : empty cE state
    | S2  : 'a cT state
    | S3  : 'a cF state
    | S4  : 'a cL state
    | S5  : 'a cI state
    | S6  : 'a cE cP state
    | S7  : 'a cT cS state
    | S8  : 'a cL cE state
    | S9  : 'a cE cP cT state
    | S10 : 'a cT cS cF state
    | S11 : 'a cL cE cR state


  let rec action : type a. a state -> token list -> a -> int =
    fun s tl stack ->
      match s, (peek tl) with
      (* S0 *)
      | S0, KInt x -> action S5 (rest tl) (SI (stack, S0, x))
      | S0, KLeft -> action S4 (rest tl) (SL (stack, S0))
      (* S1 *)
      | S1, KPlus -> action S6 (rest tl) (SP (stack, S1))
      | S1, EOF -> let SE (stack, s, v) = stack in v
      (* S2 *)
      | S2, KPlus ->
        let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
      | S2, KStar ->
        action S7 (rest tl) (SS (stack, s))
      | S2, KRight ->
        let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
      | S2, EOF ->
        let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
      (* S3 *)
      | S3, KPlus ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      | S3, KStar ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      | S3, KRight ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      | S3, EOF ->
        let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
      (* S4 *)
      | S4, KInt x -> action S5 (rest tl) (SI (stack, s, x))
      | S4, KLeft -> action S4 (rest tl) (SL (stack, s))
      (* S5 *)
      | S5, KPlus ->
        let SI (stack, s, v) = stack in
        gotoF s tl (SF (stack, s, v))
      | S5, KStar ->
        let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
      | S5, KRight ->
        let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
      | S5, EOF ->
        let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
      (* S6 *)
      | S6, KInt x -> action S5 (rest tl) (SI (stack, s, x))
      | S6, KLeft -> action S4 (rest tl) (SL (stack, s))
      (* S7 *)
      | S7, KInt x -> action S5 (rest tl) (SI (stack, s, x))
      | S7, KLeft -> action S4 (rest tl) (SL (stack, s))
      (* S8 *)
      | S8, KPlus -> action S6 (rest tl) (SP (stack, s))
      | S8, KRight -> action S11 (rest tl) (SR (stack, s))
      (* S9 *)
      | S9, KPlus ->
        let ST (SP (SE (stack, s, x), _), _, y) = stack in
        let stack = SE (stack, s, x + y) in
        gotoE s tl stack
      | S9, KStar -> action S7 (rest tl) (SS (stack, S9))
      | S9, KRight ->
        let ST (SP (SE (stack, s, x), _), _, y) = stack in
        let stack = SE (stack, s, x + y) in
        gotoE s tl stack
      | S9, EOF ->
        let ST (SP (SE (stack, s, x), _), _, y) = stack in
        let stack = SE (stack, s, x + y) in
        gotoE s tl stack
      (* S10 *)
      | S10, KPlus ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      | S10, KStar ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      | S10, KRight ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      | S10, EOF ->
        let SF (SS (ST (stack, s, x), _), _, y) = stack in
        let stack = ST (stack, s, x * y) in
        gotoT s tl stack
      (* S11 *)
      | S11, KPlus ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | S11, KStar ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | S11, KRight ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | S11, EOF ->
        let SR (SE (SL (stack, s), _, v), _) = stack in
        let stack = SF (stack, s, v) in
        gotoF s tl stack
      | _ -> failwith "Invalid grammar"

  (* switch state *)
  and gotoE : type a. a state -> token list -> a cE -> int = fun s tl stack ->
    match s with
    | S0 -> action S1 tl stack
    | S4 -> action S8 tl stack

  and gotoT : type a. a state -> token list -> a cT -> int = fun s tl stack ->
    match s with
    | S0 -> action S2 tl stack
    | S4 -> action S2 tl stack
    | S6 -> action S9 tl stack

  and gotoF : type a. a state -> token list -> a cF -> int = fun s tl stack ->
    match s with
    | S0 -> action S3 tl stack
    | S4 -> action S3 tl stack
    | S6 -> action S3 tl stack
    | S7 -> action S10 tl stack

  let test () = action S0 [KInt 3; KPlus; KInt 2; EOF] SEmpty;;
end


(* Jeremy Yallop's attempt to remove GADT *)
module GADT_Free_A =
struct

  type empty = SEmpty
  (* stack *)
  type 'a cP = 'a * 'a stateR        (* Plus *)
  and  'a cS = 'a * 'a stateR        (* Star *)
  and  'a cL = 'a * 'a stateR        (* Left *)
  and  'a cR = 'a * 'a stateR        (* Right *)
  (* last field is semantic value *)
  and  'a cI = 'a * 'a stateR * int  (* Int *)
  and  'a cE = 'a * 'a stateR * int  (* Expression *)
  and  'a cT = 'a * 'a stateR * int  (* Term *)
  and  'a cF = 'a * 'a stateR * int  (* Factor *)
  and 'a stateR = {
      gotoE : token list -> 'a cE -> int;
      gotoT : token list -> 'a cT -> int;
      gotoF : token list -> 'a cF -> int;
    }
  let gotoE {gotoE} = gotoE
  let gotoT {gotoT} = gotoT
  let gotoF {gotoF} = gotoF

  let failure _ _ = assert false
  let goto_failure = { gotoE = failure; gotoT = failure; gotoF = failure }

  let rec s0  : empty stateR = {
      gotoE = s2_action;
      gotoT = s1_action;
      gotoF = s3_action;
    }
  and s0_action = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s0, x)
    | KLeft -> s4_action (rest tl) (stack, s0)
  and s1  : empty cE stateR = goto_failure
  and s1_action = fun tl stack -> match peek tl with
    | KPlus -> s6_action (rest tl) (stack, s1)
    | EOF -> let  (stack, s, v) = stack in v

  and s2  : 'a. 'a cT stateR = goto_failure
  and s2_action : type a. token list -> a cT -> int = fun tl stack -> match peek tl with
    | KStar ->
      s7_action (rest tl) (stack, s2)
    | KPlus | KRight | EOF ->
      let  (stack, s, v) = stack in gotoE s tl (stack, s, v)

  and s3  : 'a. 'a cF stateR = goto_failure
  and s3_action : type a. token list -> a cF -> int = fun tl stack -> match peek tl with
    | KPlus|KStar|KRight|EOF ->
      let  (stack, s, v) = stack in gotoT s tl (stack, s, v)

  and s4  : 'a. 'a cL stateR = {
      gotoE = s8_action;
      gotoT = s2_action;
      gotoF = s3_action;
    }
  and s4_action : type a. token list -> a cL -> int = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s4, x)
    | KLeft -> s4_action (rest tl) (stack, s4)

  and s5  : 'a. 'a cI stateR = goto_failure
  and s5_action : type a. token list -> a cI -> int = fun tl stack -> match peek tl with
    | KPlus | KStar | KRight | EOF ->
      let  (stack, s, v) = stack in gotoF s tl (stack, s, v)

  and s6  : 'a. 'a cE cP stateR = {
      gotoE = failure;
      gotoT = s9_action;
      gotoF = s3_action;
    }
  and s6_action : type a. token list -> a cE cP -> int = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s6, x)
    | KLeft -> s4_action (rest tl) (stack, s6)

  and s7  : 'a. 'a cT cS stateR = {goto_failure with gotoF = s10_action}
  and s7_action : type a. token list -> a cT cS -> int = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s7, x)
    | KLeft -> s4_action (rest tl) (stack, s7)

  and s8  : 'a. 'a cL cE stateR = goto_failure
  and s8_action : type a. token list -> a cL cE -> int = fun tl stack -> match peek tl with
    | KPlus -> s6_action (rest tl) (stack, s8)
    | KRight -> s11_action (rest tl) (stack, s8)

  and s9  : 'a. 'a cE cP cT stateR = goto_failure
  and s9_action : type a. token list -> a cE cP cT -> int = fun tl stack -> match peek tl with
    | KPlus | KRight | EOF ->
      let  (((stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x + y) in
      gotoE s tl stack
    | KStar -> s7_action (rest tl) (stack, s9)

  and s10 : 'a. 'a cT cS cF stateR = goto_failure
  and s10_action : type a. token list -> a cT cS cF -> int = fun tl stack -> match peek tl with
    | KPlus | KStar | KRight | EOF ->
      let  (((stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x * y) in
      gotoT s tl stack

  and s11 : 'a. 'a cL cE cR stateR = goto_failure
  and s11_action : type a. token list -> a cL cE cR -> int = fun tl stack -> match peek tl with
    | KPlus | KStar | KRight | EOF ->
      let  (((stack, s), _, v), _) = stack in
      let stack =  (stack, s, v) in
      gotoF s tl stack
end

(* LALR(1) actually. We didn't use (one) lookhead to resolve
   shift/reduce conflict *)
module Stackless = struct
  
  (* E := id | E (E) *)
  
  type expr = Ident of string | Apply of expr * expr

  let expr_to_string e =
    let rec helper k e =
      match e with
    | Ident s -> k s
    | Apply (e1, e2) ->
      helper (fun s1 ->
      helper (fun s2 ->
      k (Printf.sprintf "%s (%s)" s1 s2)) e2) e1 in
    helper (fun x -> x) e

  type token = Ident of string | LPARENT | RPARENT | EOF

  type 'a parser = token list -> 'a

  let reduce_id: (expr -> 'a parser) -> string -> 'a parser =
    fun g n -> g (Ident n)

  let reduce_e_e: (expr -> 'a parser) -> expr -> expr -> 'a parser =
    fun g f x -> g (Apply (f, x))

  let rec state1 : (expr -> 'a parser) -> ('a parser) = fun k ts ->
    match ts with
    | Ident n :: tr ->
      let rec g e = state2 (reduce_e_e g e) (k e) in
      reduce_id g n tr
    | _ -> failwith "syntax error"

  and state2 : (expr -> 'a parser) -> 'a parser -> 'a parser =
    fun k1 k2 ts ->
      match ts with
      | LPARENT :: tr -> state3 k1 tr
      | EOF :: tr -> k2 tr
      | _ -> failwith "invalid syntax"

  and state3 : (expr -> 'a parser) -> ('a parser) =
    fun k ts ->
      match ts with
      | Ident n :: tr ->
        let rec g e = state4 (reduce_e_e g e) (k e) in
        reduce_id g n tr
      | _ -> failwith "invalid syntax"

  and state4 : (expr -> 'a parser) -> ('a parser) -> ('a parser) =
    fun k1 k2 ts ->
      match ts with
      | LPARENT :: tr -> state3 k1 tr
      | RPARENT :: tr -> k2 tr
      | _ -> failwith "syntax error"

  let parse_e : expr parser = state1 (fun e tl -> e)

  let test1 () =
    let tlist = [Ident "a"; LPARENT; Ident "b"; RPARENT; EOF] in
    let expr = parse_e tlist in
    print_endline (expr_to_string expr)

  let test2 () =
    let t1 = [Ident "a"; LPARENT; Ident "b"; RPARENT] in
    let t2 = [Ident "c"; LPARENT; Ident "d"; RPARENT] in
    let tl = t1 @ [LPARENT] @ t2 @ [RPARENT; EOF] in
    let expr = parse_e tl in
    print_endline (expr_to_string expr)

end

(* First stackless LR(1) parser !!!
   Grammar is from ASU86, 4.55 *)
module StacklessM455 = struct

  (*
     S -> C C
     C -> c C | d
  *)

  type token = C | D | EOF

  type 'a parser = token list -> 'a
  
  type s = S1 of c * c
  and c = C1 of c | C2

  let rec s_to_string (S1 (c1, c2)) =
    let cs1 = c_to_string c1 and cs2 = c_to_string c2 in
    Printf.sprintf "(%s %s)" cs1 cs2
  and c_to_string = function
    | C1 c -> let s = c_to_string c in Printf.sprintf "(c %s)" s
    | C2 -> "(d)"

  let log = print_endline

  let reduce_c1 : (c -> 'a parser) -> c -> 'a parser =
    fun g c -> log "reducing c1"; g (C1 c)

  let reduce_c2 : (c -> 'a parser) -> 'a parser =
    fun g -> log "reducing c2"; g C2

  let reduce_s1 : (s -> 'a parser) -> c -> c -> 'a parser =
    fun g c1 c2 -> "reducing s1"; g (S1 (c1, c2))

  let rec state0 : (s -> 'a parser) -> 'a parser = fun k ts ->
    let rec gs v = state1 (k v) and gc v = state2 (reduce_s1 gs v) in
    match ts with
    | C :: tr -> state3 (reduce_c1 gc) tr
    | D :: tr -> state4 (reduce_c2 gc) tr
    | _ -> failwith "0: expecting C/D"

  and state1 : 'a parser -> 'a parser = fun k ts ->
    match ts with
    | [EOF] -> k ts
    | _ -> failwith "1: reducing only on EOF"

  and state2 : (c -> 'a parser) -> 'a parser = fun k ts ->
    let gc v = state5 (k v) in
    match ts with
    | C :: tr -> state6 (reduce_c1 gc) tr
    | D :: tr -> state7 (reduce_c2 gc) tr
    | _ -> failwith "2: expecting C/D"

  and state3 : (c -> 'a parser) -> 'a parser = fun k ts ->
    let gc v = state8 (k v) in
    match ts with
    | C :: tr -> state3 (reduce_c1 gc) tr
    | D :: tr -> state4 (reduce_c2 gc) tr
    | _ -> failwith "3: expecting C/D"

  and state4 : 'a parser -> 'a parser = fun k ts ->
    match ts with
    | C :: tr -> log "4: reducing c"; k ts
    | D :: tr -> log "4: reducing d"; k ts
    | _ -> failwith "4: reducing only on C/D"

  and state5 : 'a parser -> 'a parser = fun k ts ->
    match ts with
    | [EOF] -> k ts
    | _ -> failwith "5: reducing only on EOF"

  and state6 : (c -> 'a parser) -> 'a parser = fun k ts ->
    let gc v = state9 (k v) in
    match ts with
    | C :: tr -> state6 (reduce_c1 gc) tr
    | D :: tr -> state7 (reduce_c2 gc) tr
    | _ -> failwith "6: expecting C/D"

  and state7 : 'a parser -> 'a parser = fun k ts ->
    match ts with
    | [EOF] -> k ts
    | _ -> failwith "7: reducing only on EOF"

  and state8 : 'a parser -> 'a parser = fun k ts ->
    match ts with
    | C :: tr | D :: tr -> k ts
    | _ -> failwith "8: reducing only on C/D"

  and state9 : 'a parser -> 'a parser = fun k ts ->
    match ts with
    | [EOF] -> k ts
    | _ -> failwith "9: reducing only on EOF"

  let parse_s : s parser = state0 (fun e tl -> e)

  let test1 () =
    let token = [C; C; C; D; C; C; D; EOF] in
    let s = parse_s token in
    print_endline (s_to_string s)

end

let () = StacklessM455.test1 ()
