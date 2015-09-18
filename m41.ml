(* Aho 4.1 *)

type token =
  KPlus | KStar | KLeft | KRight | KEnd | KInt of int | EOF

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

let peek = List.hd and rest = List.tl

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
       let local : type a. a cI -> int =
          fun (type a) (stack : a cI) -> 
           let SI ((stack : a), (s : a state), (v : int)) = (stack : a cI) in
             gotoF (s : a state) tl (SF ((stack : a), (s : a state), (v : int)))
           in
          local stack
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

module GADT_free =
struct
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

  let rec s0  : empty stateR = {
      gotoE = s0_gotoE;
      gotoT = s0_gotoT;
      gotoF = s0_gotoF;
    } 
  and s0_action = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s0, x)
    | KLeft -> s4_action (rest tl) (stack, s0)
  and s0_gotoE tl stack = s1_action tl stack
  and s0_gotoT : token list -> empty cT -> int = fun tl stack ->
      s2_action tl stack
  and s0_gotoF : token list -> empty cF -> int = fun tl stack ->
      s3_action tl stack
  and s1  : empty cE stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s1_action = fun tl stack -> match peek tl with
    | KPlus -> s6_action (rest tl) (stack, s1)
    | EOF -> let  (stack, s, v) = stack in v

  and s2  : 'a. 'a cT stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    } 
  and s2_action : type a. token list -> a cT -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let  (stack, s, v) = stack in gotoE s tl (stack, s, v)
    | KStar ->
      s7_action (rest tl) (stack, s2)
    | KRight ->
      let  (stack, s, v) = stack in gotoE s tl (stack, s, v)
    | EOF ->
      let  (stack, s, v) = stack in gotoE s tl (stack, s, v)

  and s3  : 'a. 'a cF stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    } 
  and s3_action : type a. token list -> a cF -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let  (stack, s, v) = stack in gotoT s tl (stack, s, v)
    | KStar ->
      let  (stack, s, v) = stack in gotoT s tl (stack, s, v)
    | KRight ->
      let  (stack, s, v) = stack in gotoT s tl (stack, s, v)
    | EOF ->
      let  (stack, s, v) = stack in gotoT s tl (stack, s, v)

  and s4  : 'a. 'a cL stateR = {
      gotoE = s4_gotoE;
      gotoT = s4_gotoT;
      gotoF = s4_gotoF;
    } 
  and s4_action : type a. token list -> a cL -> int = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s4, x)
    | KLeft -> s4_action (rest tl) (stack, s4)
  and s4_gotoE : type a. token list -> a cL cE -> int = fun tl stack ->
      s8_action tl stack
  and s4_gotoT : type a. token list -> a cL cT -> int = fun tl stack ->
      s2_action tl stack
  and s4_gotoF : type a. token list -> a cL cF -> int = fun tl stack ->
      s3_action tl stack
  and s5  : 'a. 'a cI stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    } 
  and s5_action : type a. token list -> a cI -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let  (stack, s, v) = stack in gotoF s tl (stack, s, v)
    | KStar ->
      let  (stack, s, v) = stack in gotoF s tl (stack, s, v)
    | KRight ->
      let  (stack, s, v) = stack in gotoF s tl (stack, s, v)
    | EOF ->
      let  (stack, s, v) = stack in gotoF s tl (stack, s, v)
  and s6  : 'a. 'a cE cP stateR = {
      gotoE = failure;
      gotoT = s6_gotoT;
      gotoF = s6_gotoF;
    } 
  and s6_action : type a. token list -> a cE cP -> int = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s6, x)
    | KLeft -> s4_action (rest tl) (stack, s6)
  and s6_gotoT : type a. token list -> a cE cP cT -> int = fun tl stack ->
      s9_action tl stack
  and s6_gotoF : type a. token list -> a cE cP cF -> int = fun tl stack ->
      s3_action tl stack

  and s7  : 'a. 'a cT cS stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = s7_gotoF;
    } 
  and s7_action : type a. token list -> a cT cS -> int = fun tl stack -> match peek tl with
    | KInt x -> s5_action (rest tl) (stack, s7, x)
    | KLeft -> s4_action (rest tl) (stack, s7)
  and s7_gotoF : type a. token list -> a cT cS cF -> int = fun tl stack ->
      s10_action tl stack

  and s8  : 'a. 'a cL cE stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    } 
  and s8_action : type a. token list -> a cL cE -> int = fun tl stack -> match peek tl with
    | KPlus -> s6_action (rest tl) (stack, s8)
    | KRight -> s11_action (rest tl) (stack, s8)

  and s9  : 'a. 'a cE cP cT stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    } 
  and s9_action : type a. token list -> a cE cP cT -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let  ( ( (stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x + y) in
      gotoE s tl stack
    | KStar -> s7_action (rest tl) (stack, s9)
    | KRight ->
      let  ( ( (stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x + y) in
      gotoE s tl stack
    | EOF ->
      let  ( ( (stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x + y) in
      gotoE s tl stack

  and s10 : 'a. 'a cT cS cF stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    } 
  and s10_action : type a. token list -> a cT cS cF -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let  ( ( (stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x * y) in
      gotoT s tl stack
    | KStar ->
      let  ( ( (stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x * y) in
      gotoT s tl stack
    | KRight ->
      let  ( ( (stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x * y) in
      gotoT s tl stack
    | EOF ->
      let  ( ( (stack, s, x), _), _, y) = stack in
      let stack =  (stack, s, x * y) in
      gotoT s tl stack

  and s11 : 'a. 'a cL cE cR stateR = {
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    } 
  and s11_action : type a. token list -> a cL cE cR -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let  ( ( (stack, s), _, v), _) = stack in
      let stack =  (stack, s, v) in
      gotoF s tl stack
    | KStar ->
      let  ( ( (stack, s), _, v), _) = stack in
      let stack =  (stack, s, v) in
      gotoF s tl stack
    | KRight ->
      let  ( ( (stack, s), _, v), _) = stack in
      let stack =  (stack, s, v) in
      gotoF s tl stack
    | EOF ->
      let  ( ( (stack, s), _, v), _) = stack in
      let stack =  (stack, s, v) in
      gotoF s tl stack
end


