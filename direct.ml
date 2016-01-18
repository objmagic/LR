module StacklessM455_direct = struct
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

  let reduce_c1 : c -> c =
    fun c -> C1 c

  let reduce_c2 : c =
    C2

  let reduce_s1 : c -> c -> s =
    fun c1 c2 -> S1 (c1, c2)

  let rec state0 : token list -> s * token list = fun ts ->
    match ts with
    | C :: tr ->
      let (c0, ts) = state3 tr in
      let c1 = reduce_c1 c0 in
      let (c2, ts) = state2 ts in
      let s = reduce_s1 c1 c2 in
      (s, state1 ts)
    | D :: tr ->
      let ts = state4 tr in
      let c1 = reduce_c2 in
      let (c2, ts) = state2 ts in
      let s = reduce_s1 c1 c2 in
      (s, state1 ts)
    | _ -> failwith "0: expecting C/D"

  and state1 : token list -> token list = fun ts ->
    match ts with
    | [EOF] -> ts
    | _ -> failwith "1: reducing only on EOF"

  and state2 : token list -> c * token list = fun ts ->
    match ts with
    | C :: tr -> 
      let (c, ts) = state6 tr in
      let r = reduce_c1 c in
      (r, state5 ts)
    | D :: tr ->
      let ts = state7 tr in
      let x = reduce_c2  in
      (x, state5 ts)
    | _ -> failwith "2: expecting C/D"

  and state3 : token list -> c * token list = fun ts ->
    match ts with
    | C :: tr ->
      let (x, ts) = state3 tr in
      let x = reduce_c1 x in
      (x, state8 ts)
    | D :: tr ->
      let ts = state4 tr in
      let x = reduce_c2  in
      (x, state8 ts)
    | _ -> failwith "3: expecting C/D"

  and state4 : token list -> token list = fun ts ->
    match ts with
    | C :: tr -> ts
    | D :: tr -> ts
    | _ -> failwith "4: reducing only on C/D"

  and state5 : token list -> token list = fun ts ->
    match ts with
    | [EOF] -> ts
    | _ -> failwith "5: reducing only on EOF"

  and state6 : token list -> c * token list = fun ts ->
    match ts with
    | C :: tr ->
      let (x, ts) = state6 tr in
      let x = reduce_c1 x in
      (x, state9 ts)
    | D :: tr ->
      let ts = state7 tr in
      let x = reduce_c2 in
      (x, state9 ts)
    | _ -> failwith "6: expecting C/D"

  and state7 : token list -> token list = fun ts ->
    match ts with
    | [EOF] -> ts
    | _ -> failwith "7: reducing only on EOF"

  and state8 : token list -> token list = fun ts ->
    match ts with
    | C :: tr -> ts
    | D :: tr -> ts
    | _ -> failwith "8: reducing only on C/D"

  and state9 : token list -> token list = fun ts ->
    match ts with
    | [EOF] -> ts
    | _ -> failwith "9: reducing only on EOF"

  let parse_s : s parser =
    fun toks -> let e, tl = state0 toks in e

  let test1 () =
    let token = [C; C; C; D; C; C; D; EOF] in
    let s = parse_s token in
    print_endline (s_to_string s)
end
