(* Goal: (G)ADT free

   Current: we still have type definition and type ascription *)

type token =
  KPlus | KStar | KLeft | KRight | KInt of int | EOF

type empty = SEmpty

let peek = List.hd and rest = List.tl

module GADT_free =
struct

  let peek = List.hd and rest = List.tl

  (* stack *)
  type 'a cP = SP : 'a * 'a stateR       -> 'a cP (* Plus *)
  and  'a cS = SS : 'a * 'a stateR       -> 'a cS (* Star *)
  and  'a cL = SL : 'a * 'a stateR       -> 'a cL (* Left *)
  and  'a cR = SR : 'a * 'a stateR       -> 'a cR (* Right *)

  (* last field is semantic value *)
  and  'a cI = SI : 'a * 'a stateR * int -> 'a cI (* Int *)
  and  'a cE = SE : 'a * 'a stateR * int -> 'a cE (* Expression *)
  and  'a cT = ST : 'a * 'a stateR * int -> 'a cT (* Term *)
  and  'a cF = SF : 'a * 'a stateR * int -> 'a cF (* Factor *)

  and 'a stateR = {
      action: token list -> 'a -> int;
      gotoE : token list -> 'a cE -> int;
      gotoT : token list -> 'a cT -> int;
      gotoF : token list -> 'a cF -> int;
    }

  let action {action} = action
  let gotoE {gotoE} = gotoE
  let gotoT {gotoT} = gotoT
  let gotoF {gotoF} = gotoF

  let failure _ _ = assert false

  let rec s0  : empty stateR = {
      action = s0_action;
      gotoE = s0_gotoE;
      gotoT = s0_gotoT;
      gotoF = s0_gotoF;
    }
  and s0_action = fun tl stack -> match peek tl with
    | KInt x -> action s5 (rest tl) (SI (stack, s0, x))
    | KLeft -> action s4 (rest tl) (SL (stack, s0))
  and s0_gotoE tl stack = action s1 tl stack
  and s0_gotoT : token list -> empty cT -> int = fun tl stack ->
      action s2 tl stack
  and s0_gotoF : token list -> empty cF -> int = fun tl stack ->
      action s3 tl stack
  and s1  : empty cE stateR = {
      action = s1_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s1_action = fun tl stack -> match peek tl with
    | KPlus -> action s6 (rest tl) (SP (stack, s1))
    | EOF -> let SE (stack, s, v) = stack in v

  and s2  : 'a. 'a cT stateR = {
      action = s2_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s2_action : type a. token list -> a cT -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
    | KStar ->
      action s7 (rest tl) (SS (stack, s2))
    | KRight ->
      let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))
    | EOF ->
      let ST (stack, s, v) = stack in gotoE s tl (SE (stack, s, v))

  and s3  : 'a. 'a cF stateR = {
      action = s3_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s3_action : type a. token list -> a cF -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
    | KStar ->
      let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
    | KRight ->
      let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))
    | EOF ->
      let SF (stack, s, v) = stack in gotoT s tl (ST (stack, s, v))

  and s4  : 'a. 'a cL stateR = {
      action = s4_action;
      gotoE = s4_gotoE;
      gotoT = s4_gotoT;
      gotoF = s4_gotoF;
    }
  and s4_action : type a. token list -> a cL -> int = fun tl stack -> match peek tl with
    | KInt x -> action s5 (rest tl) (SI (stack, s4, x))
    | KLeft -> action s4 (rest tl) (SL (stack, s4))
  and s4_gotoE : type a. token list -> a cL cE -> int = fun tl stack ->
      action s8 tl stack
  and s4_gotoT : type a. token list -> a cL cT -> int = fun tl stack ->
      action s2 tl stack
  and s4_gotoF : type a. token list -> a cL cF -> int = fun tl stack ->
      action s3 tl stack
  and s5  : 'a. 'a cI stateR = {
      action = s5_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s5_action : type a. token list -> a cI -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
    | KStar ->
      let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
    | KRight ->
      let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
    | EOF ->
      let SI (stack, s, v) = stack in gotoF s tl (SF (stack, s, v))
  and s6  : 'a. 'a cE cP stateR = {
      action = s6_action;
      gotoE = failure;
      gotoT = s6_gotoT;
      gotoF = s6_gotoF;
    }
  and s6_action : type a. token list -> a cE cP -> int = fun tl stack -> match peek tl with
    | KInt x -> action s5 (rest tl) (SI (stack, s6, x))
    | KLeft -> action s4 (rest tl) (SL (stack, s6))
  and s6_gotoT : type a. token list -> a cE cP cT -> int = fun tl stack ->
      action s9 tl stack
  and s6_gotoF : type a. token list -> a cE cP cF -> int = fun tl stack ->
      action s3 tl stack

  and s7  : 'a. 'a cT cS stateR = {
      action = s7_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = s7_gotoF;
    }
  and s7_action : type a. token list -> a cT cS -> int = fun tl stack -> match peek tl with
    | KInt x -> action s5 (rest tl) (SI (stack, s7, x))
    | KLeft -> action s4 (rest tl) (SL (stack, s7))
  and s7_gotoF : type a. token list -> a cT cS cF -> int = fun tl stack ->
      action s10 tl stack

  and s8  : 'a. 'a cL cE stateR = {
      action = s8_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s8_action : type a. token list -> a cL cE -> int = fun tl stack -> match peek tl with
    | KPlus -> action s6 (rest tl) (SP (stack, s8))
    | KRight -> action s11 (rest tl) (SR (stack, s8))

  and s9  : 'a. 'a cE cP cT stateR = {
      action = s9_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s9_action : type a. token list -> a cE cP cT -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let ST (SP (SE (stack, s, x), _), _, y) = stack in
      let stack = SE (stack, s, x + y) in
      gotoE s tl stack
    | KStar -> action s7 (rest tl) (SS (stack, s9))
    | KRight ->
      let ST (SP (SE (stack, s, x), _), _, y) = stack in
      let stack = SE (stack, s, x + y) in
      gotoE s tl stack
    | EOF ->
      let ST (SP (SE (stack, s, x), _), _, y) = stack in
      let stack = SE (stack, s, x + y) in
      gotoE s tl stack

  and s10 : 'a. 'a cT cS cF stateR = {
      action = s10_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }
  and s10_action : type a. token list -> a cT cS cF -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let SF (SS (ST (stack, s, x), _), _, y) = stack in
      let stack = ST (stack, s, x * y) in
      gotoT s tl stack
    | KStar ->
      let SF (SS (ST (stack, s, x), _), _, y) = stack in
      let stack = ST (stack, s, x * y) in
      gotoT s tl stack
    | KRight ->
      let SF (SS (ST (stack, s, x), _), _, y) = stack in
      let stack = ST (stack, s, x * y) in
      gotoT s tl stack
    | EOF ->
      let SF (SS (ST (stack, s, x), _), _, y) = stack in
      let stack = ST (stack, s, x * y) in
      gotoT s tl stack

  and s11 : 'a. 'a cL cE cR stateR = {
      action = s11_action;
      gotoE = failure;
      gotoT = failure;
      gotoF = failure;
    }

  and s11_action : type a. token list -> a cL cE cR -> int = fun tl stack -> match peek tl with
    | KPlus ->
      let SR (SE (SL (stack, s), _, v), _) = stack in
      let stack = SF (stack, s, v) in
      gotoF s tl stack
    | KStar ->
      let SR (SE (SL (stack, s), _, v), _) = stack in
      let stack = SF (stack, s, v) in
      gotoF s tl stack
    | KRight ->
      let SR (SE (SL (stack, s), _, v), _) = stack in
      let stack = SF (stack, s, v) in
      gotoF s tl stack
    | EOF ->
      let SR (SE (SL (stack, s), _, v), _) = stack in
      let stack = SF (stack, s, v) in
      gotoF s tl stack
end

let test () =
  let open GADT_free in
  let l = [KInt 3; KPlus; KInt 4; KStar; KInt 5; EOF] in
  assert (23 = action s0 l SEmpty)

let () =
  test ()

