(* Early experiment of LR parser staging by Jeremy *)

(* Very simple arithmetic grammar
   [9.23 in Grune and Jacobs]

 1.   S → E
 2.   E → E - T
 3.   E → T
 4.   T → n
 5.   T → ( E )

*)

type terminal = [`NUM | `MINUS | `LPAREN | `RPAREN | `EOF]
type nonterminal = [`S | `E | `T]
type symbol = [terminal | nonterminal]

let string_of_terminal : terminal -> string = function
  | `NUM -> "n"
  | `MINUS -> "-"
  | `LPAREN -> "("
  | `RPAREN -> ")"
  | `EOF -> "#"

let string_of_nonterminal : nonterminal -> string = function
  | `S -> "S"
  | `E -> "E"
  | `T -> "T"

let string_of_symbol : symbol -> string = function
  | #terminal as t -> string_of_terminal t
  | #nonterminal as n -> string_of_nonterminal n

let rules = [|
  (`S, [|`E|]);
  (`E, [|`E; `MINUS; `T|]);
  (`E, [|`T|]);
  (`T, [|`NUM|]);
  (`T, [|`LPAREN; `NUM; `RPAREN|]);
|]

(* Action and Goto tables
   [9.28 in Grune and Jacobs] *)
type entry = Shift | Error | Reduce of int

let action =
  let s = Shift and r n = Reduce n and e = Error in
  [|
    [||]; (* 1-indexing *)
    [|s ; e   ; s  ; e  ; e   |];
    [|e ; r 3 ; e  ; e  ; r 3 |];
    [|e ; r 4 ; e  ; e  ; r 4 |];
    [|e ; s   ; e  ; e  ; r 1 |];
    [| (* State 5 is missing: see the book *) |];
    [|s ; e   ; s  ; e  ; e   |];
    [|s ; e   ; s  ; e  ; e   |];
    [|e ; r 2 ; e  ; e  ; r 2 |];
    [|e ; r 3 ; e  ; r 3; e   |];
    [|e ; r 4 ; e  ; r 4; e   |];
    [|e ; s   ; e  ; s  ; e   |];
    [|e ; r 5 ; e  ; e  ; r 5 |];
    [|s ; e   ; s  ; e  ; e   |];
    [|s ; e   ; s  ; e  ; e   |];
    [|e ; r 2 ; e  ; r 2; e   |];
    [|e ; s   ; e  ; s  ; e   |];
    [|e ; r 5 ; e  ; r 5; e   |];
  |]

let error = 0
let accept = -1

let goto =
  let e = error and a = accept in
  [|
    [||]; (* 1-indexing *)
    [|3 ;e ;6 ;e ;e ;a ;4 ;2|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
    [|0 ;7 ;e ;e ;e ;e ;e ;e|];
    [| (* State 5 is missing: see the book *) |];
    [|10;e ;13;e ;e ;e ;11;9|];
    [|3 ;e ;6 ;e ;e ;e ;e ;8|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
    [|0 ;14;e ;12;e ;e ;e ;e|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
    [|10;e ;13;e ;e ;e ;16;9|];
    [|10;e ;13;e ;e ;e ;e ;15|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
    [|0 ;14;e ;17;e ;e ;e ;e|];
    [|0 ;e ;e ;e ;e ;e ;e ;e|];
  |]

let token_number : terminal -> int = function
  | `NUM -> 0
  | `MINUS -> 1
  | `LPAREN -> 2
  | `RPAREN -> 3
  | `EOF -> 4

let symbol_number : symbol -> int = function
  | #terminal as t -> token_number t
  | `S -> 5
  | `E -> 6
  | `T -> 7

module Stack :
sig
  type stack_entry = symbol * int
  type t = { top: int; rest: stack_entry list }
  val initial : state:int -> t
  val push : symbol -> state:int -> t -> t
  val drop2N : int -> t -> t
  val string_of : t -> string
  val top : t -> int
end =
struct
  type stack_entry = symbol * int
  type t = { top: int; rest: stack_entry list }

  let string_of_stack_entry (sym, state) =
    Printf.sprintf "<%d> %s" state (string_of_symbol sym)

  let string_of {top; rest} =
    Printf.sprintf "%s%s<%d>"
      (String.concat " " (List.rev_map string_of_stack_entry rest))
      (match rest with [] -> "" | _ -> " ")
      top

  let rec drop2N n s =
    if n = 0 then s else
      match s.rest with
        [] -> assert false
      | (_, top) :: rest -> drop2N (pred n) { top; rest }

  let push term ~state {top; rest} =
    {top = state; rest = (term, top) :: rest }

  let initial ~state = { top = state; rest = [] }

  let top {top} = top
end

let string_of_input input =
  String.concat "" (List.map string_of_terminal input)

let string_of_action = function
  | Shift -> "shift"
  | Reduce n -> Printf.sprintf "reduce %d" n
  | Error -> "error"

let print_state stack input action =
  Printf.printf "%-50s%10s %s\n"
    (Stack.string_of stack)
    (string_of_input input)
    (string_of_action action);
  flush stdout

(* Parsing with the Goto and Action tables *)
let rec parse stack input =
  if Stack.top stack <> accept then
  let next_token = List.hd input in
  let next_action = action.(Stack.top stack).(token_number next_token) in
  print_state stack input next_action;
  match next_action, input with
  | Shift, next_token :: rest ->
      let next_state = goto.(Stack.top stack).(token_number next_token) in
      parse (Stack.push (next_token :> symbol) next_state stack) rest
  | Reduce n, _ ->
      let lhs, rhs = rules.(pred n) in
      let stack = Stack.drop2N (Array.length rhs) stack in
      let next_state = goto.(Stack.top stack).(symbol_number lhs) in
      parse (Stack.push lhs next_state stack) input
  | Error, _ -> failwith "parse error"
  | Shift, []  -> failwith "unexpected EOF"


(* Partial evaluation, treating the Goto, Action and rules tables as static *)
module Partial_eval =
struct

  (*
     1: apply The Trick to Stack.top stack
     2: perform action table lookups statically (simplifying pattern-matching)
     3: perform calls to 'pred' statically
     4: perform calls to 'token_number' statically
     5: perform rules lookups statically
     6: perform Array.length rhs statically
     7: perform symbol_number statically
     8: merge the error cases
     9: inline goto lookups where statically known
     10: merge the reduce cases (all cases with the same index can be merged)
     11: merge the shift cases (all cases with the same next_token and goto entry can be merged.  we could perhaps do better by merging cases which don't have the same next_token)
     12: specialize/unroll drop2N, since the lengths of all productions are known
     13: inline push
     14: split out top and rest from the stack
     15: specialize Goto by columns, since the columns are always known
     16: perform The Trick on the Goto lookup

   We should also
  *)

  let rec parse top rest input =
    let stack = { Stack.top; rest} in
    match top, rest, input with
    (* accept cases *)
    | -1, _, _ -> ()

    (* reduce cases *)
    | 4, (_, 1) :: rest, `EOF :: _ ->
      print_state stack input (Reduce 1);
      parse accept ((`S, 1) :: rest) input
    | 8, _ :: _ :: (_, 1) :: rest, (`MINUS|`EOF) :: _
    | 15, _ :: _ :: (_, 1) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 2);
      parse 4 ((`E, 1) :: rest) input
    | 8, _ :: _ :: (_, 6) :: rest, (`MINUS|`EOF) :: _
    | 15, _ :: _ :: (_, 6) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 2);
      parse 11 ((`E, 6) :: rest) input
    | 8, _ :: _ :: (_, 13) :: rest, (`MINUS|`EOF) :: _
    | 15, _ :: _ :: (_, 13) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 2);
      parse 16 ((`E, 13) :: rest) input
    | 2, (_, 1) :: rest, (`MINUS|`EOF) :: _
    | 9, (_, 1) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 3);
      parse 4 ((`E, 1) :: rest) input
    | 2, (_, 6) :: rest, (`MINUS|`EOF) :: _
    | 9, (_, 6) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 3);
      parse 11 ((`E, 6) :: rest) input
    | 2, (_, 13) :: rest, (`MINUS|`EOF) :: _
    | 9, (_, 13) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 3);
      parse 16 ((`E, 13) :: rest) input
    | 3, (_, 1) :: rest, (`EOF|`MINUS) :: _
    | 10, (_, 1) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 4);
      parse 2 ((`T, 1) :: rest) input
    | 3, (_, 6) :: rest, (`EOF|`MINUS) :: _
    | 10, (_, 6) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 4);
      parse 9 ((`T, 6) :: rest) input
    | 3, (_, 7) :: rest, (`EOF|`MINUS) :: _
    | 10, (_, 7) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 4);
      parse 8 ((`T, 7) :: rest) input
    | 3, (_, 13) :: rest, (`EOF|`MINUS) :: _
    | 10, (_, 13) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 4);
      parse 9 ((`T, 13) :: rest) input
    | 3, (_, 14) :: rest, (`EOF|`MINUS) :: _
    | 10, (_, 14) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 4);
      parse 15 ((`T, 14) :: rest) input
    | 12, _ :: _ :: (_, 1) :: rest, (`MINUS|`EOF) :: _
    | 17, _ :: _ :: (_, 1) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 5);
      parse 2 ((`T, 1) :: rest) input
    | 12, _ :: _ :: (_, 6) :: rest, (`MINUS|`EOF) :: _
    | 17, _ :: _ :: (_, 6) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 5);
      parse 9 ((`T, 6) :: rest) input
    | 12, _ :: _ :: (_, 7) :: rest, (`MINUS|`EOF) :: _
    | 17, _ :: _ :: (_, 7) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 5);
      parse 8 ((`T, 7) :: rest) input
    | 12, _ :: _ :: (_, 13) :: rest, (`MINUS|`EOF) :: _
    | 17, _ :: _ :: (_, 13) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 5);
      parse 9 ((`T, 13) :: rest) input
    | 12, _ :: _ :: (_, 14) :: rest, (`MINUS|`EOF) :: _
    | 17, _ :: _ :: (_, 14) :: rest, (`MINUS|`RPAREN) :: _ ->
      print_state stack input (Reduce 5);
      parse 15 ((`T, 14) :: rest) input

    (* shift cases *)
    | (6|13|14), rest, `NUM :: input ->
      print_state stack input Shift;
      parse 10 ((`NUM, top) :: rest) input
    | (1|7), rest, `NUM :: input ->
      print_state stack input Shift;
      parse 3 ((`NUM, top) :: rest) input
    | (1|7), rest, `LPAREN :: input ->
      print_state stack input Shift;
      parse 6 ((`LPAREN, top) :: rest) input
    | (6|13|14), rest, `LPAREN :: input ->
      print_state stack input Shift;
      parse 13 ((`LPAREN, top) :: rest) input
    | 4, rest, `MINUS :: input ->
      print_state stack input Shift;
      parse 7 ((`MINUS, top) :: rest) input
    | (11|16), rest, `MINUS :: input ->
      print_state stack input Shift;
      parse 14 ((`MINUS, top) :: rest) input
    | 11, rest, `RPAREN :: input ->
      print_state stack input Shift;
      parse 12 ((`RPAREN, top) :: rest) input
    | 16, rest, `RPAREN :: input ->
      print_state stack input Shift;
      parse 17 ((`RPAREN, top) :: rest) input

    (* Error cases *)
    | 1, _, (`MINUS|`RPAREN|`EOF) :: _
    | 2, _, (`NUM|`LPAREN|`RPAREN) :: _
    | 3, _, (`NUM|`LPAREN|`RPAREN) :: _
    | 4, _, (`NUM|`LPAREN|`RPAREN) :: _
    | 6, _, (`MINUS|`RPAREN|`EOF) :: _
    | 7, _, (`MINUS|`RPAREN|`EOF) :: _
    | 8, _, (`NUM|`LPAREN|`RPAREN) :: _
    | 9, _, (`NUM|`LPAREN|`EOF) :: _
    | 10, _, (`NUM|`LPAREN|`EOF) :: _
    | 11, _, (`NUM|`LPAREN|`EOF) :: _
    | 12, _, (`NUM|`LPAREN|`RPAREN) :: _
    | 13, _, (`MINUS|`RPAREN|`EOF) :: _
    | 14, _, (`MINUS|`RPAREN|`EOF) :: _
    | 15, _, (`NUM|`LPAREN|`EOF) :: _
    | 16, _, (`NUM|`LPAREN|`EOF) :: _
    | 17, _, (`NUM|`LPAREN|`EOF) :: _ -> failwith "parse error"
    | n, _, [] -> Printf.kprintf failwith "unexpected EOF"
    | n, _, tok :: _ -> Printf.kprintf failwith "error %d %s" n (string_of_terminal tok)
end

module Partial_eval_refunctionalized =
struct
  (* Turn the partially-evaluated parse function into a family of functions,
     one for each stack-top state.

     It's pretty straightforward, since the first argument to parse (i.e. the
     top of the stack) is always known when making a call.

     1. gather all the cases with the same stack-top together.

     2. Split into multiple functions by stack-top and have parse dispatch to
        those functions

     3. Specialize the calls.

     Actually, we may need a second round to eliminate the matching on the rest of the stack.
     (This is starting to look like it's going to turn the table-based parser into recursive-ascent.)

     However, it's not entirely clear whether we can eliminate *all* the stack
     matching: do we have enough context when we push/call to eliminate *all*
     the matching?

     Why are some states unreachable?
     e.g. parse_3 is only ever called with 1 or 7 at the top of the stack
     so what are the other cases for?

     I think some states are unreachable because of merges.
  *)

  let pr top rest input action =
    print_state { Stack.top; rest } input action

  let rec parse_1 rest input =
    match rest, input with
    | rest, `NUM :: input -> pr 1 rest input Shift; parse_3 ((`NUM, 1) :: rest) input
    | rest, `LPAREN :: input -> pr 1 rest input Shift; parse_6 ((`LPAREN, 1) :: rest) input
    | _, (`MINUS|`RPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
  and parse_2 rest input =
    match rest, input with
    | (_, 1) :: rest, (`MINUS|`EOF) :: _ -> pr 2 rest input (Reduce 3); parse_4 ((`E, 1) :: rest) input
    | _, (`NUM|`LPAREN|`RPAREN) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_3 rest input =
    match rest, input with
    | (_, 1) :: rest, (`EOF|`MINUS) :: _ -> pr 3 rest input (Reduce 4); parse_2 ((`T, 1) :: rest) input
    | (_, 7) :: rest, (`EOF|`MINUS) :: _ -> pr 3 rest input (Reduce 4); parse_8 ((`T, 7) :: rest) input
    | _, (`NUM|`LPAREN|`RPAREN) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_4 rest input =
    match rest, input with
    | (_, 1) :: rest, `EOF :: _ -> pr 4 rest input (Reduce 1); parse_accept ((`S, 1) :: rest) input
    | rest, `MINUS :: input -> pr 4 rest input Shift; parse_7 ((`MINUS, 4) :: rest) input
    | _, (`NUM|`LPAREN|`RPAREN) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)
  and parse_6 rest input =
    match rest, input with
    | rest, `NUM :: input -> pr 6 rest input Shift; parse_10 ((`NUM, 6) :: rest) input
    | rest, `LPAREN :: input -> pr 6 rest input Shift; parse_13 ((`LPAREN, 6) :: rest) input
    | _, (`MINUS|`RPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"

  and parse_7 rest input =
    match rest, input with
    | rest, `NUM :: input -> pr 7 rest input Shift; parse_3 ((`NUM, 7) :: rest) input
    | rest, `LPAREN :: input -> pr 7 rest input Shift; parse_6 ((`LPAREN, 7) :: rest) input
    | _, (`MINUS|`RPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"

  and parse_8 rest input =
    match rest, input with
    | _ :: _ :: (_, 1) :: rest, (`MINUS|`EOF) :: _ -> pr 8 rest input (Reduce 2); parse_4 ((`E, 1) :: rest) input
    | _ :: _ :: (_, 6) :: rest, (`MINUS|`EOF) :: _ -> pr 8 rest input (Reduce 2); parse_11 ((`E, 6) :: rest) input
    | _ :: _ :: (_, 13) :: rest, (`MINUS|`EOF) :: _ -> pr 8 rest input (Reduce 2); parse_16 ((`E, 13) :: rest) input
    | _, (`NUM|`LPAREN|`RPAREN) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_9 rest input =
    match rest, input with
    | (_, 6) :: rest, (`MINUS|`RPAREN) :: _ -> pr 9 rest input (Reduce 3); parse_11 ((`E, 6) :: rest) input
    | (_, 13) :: rest, (`MINUS|`RPAREN) :: _ -> pr 9 rest input (Reduce 3); parse_16 ((`E, 13) :: rest) input
    | _, (`NUM|`LPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_10 rest input =
    match rest, input with
    | (_, 6) :: rest, (`MINUS|`RPAREN) :: _ -> pr 10 rest input (Reduce 4); parse_9 ((`T, 6) :: rest) input
    | (_, 13) :: rest, (`MINUS|`RPAREN) :: _ -> pr 10 rest input (Reduce 4); parse_9 ((`T, 13) :: rest) input
    | (_, 14) :: rest, (`MINUS|`RPAREN) :: _ -> pr 10 rest input (Reduce 4); parse_15 ((`T, 14) :: rest) input
    | _, (`NUM|`LPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_11 rest input =
    match rest, input with
    | rest, `MINUS :: input -> pr 11 rest input Shift; parse_14 ((`MINUS, 11) :: rest) input
    | rest, `RPAREN :: input -> pr 11 rest input Shift; parse_12 ((`RPAREN, 11) :: rest) input
    | _, (`NUM|`LPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"

  and parse_12 rest input =
    match rest, input with
    | _ :: _ :: (_, 1) :: rest, (`MINUS|`EOF) :: _ -> pr 12 rest input (Reduce 5); parse_2 ((`T, 1) :: rest) input
    | _ :: _ :: (_, 6) :: rest, (`MINUS|`EOF) :: _ -> pr 12 rest input (Reduce 5); parse_9 ((`T, 6) :: rest) input
    | _ :: _ :: (_, 7) :: rest, (`MINUS|`EOF) :: _ -> pr 12 rest input (Reduce 5); parse_8 ((`T, 7) :: rest) input
    | _ :: _ :: (_, 13) :: rest, (`MINUS|`EOF) :: _ -> pr 12 rest input (Reduce 5); parse_9 ((`T, 13) :: rest) input
    | _ :: _ :: (_, 14) :: rest, (`MINUS|`EOF) :: _ -> pr 12 rest input (Reduce 5); parse_15 ((`T, 14) :: rest) input
    | _, (`NUM|`LPAREN|`RPAREN) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_13 rest input =
    match rest, input with
    | rest, `NUM :: input -> pr 13 rest input Shift; parse_10 ((`NUM, 13) :: rest) input
    | rest, `LPAREN :: input -> pr 13 rest input Shift; parse_13 ((`LPAREN, 13) :: rest) input
    | _, (`MINUS|`RPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"

  and parse_14 rest input =
    match rest, input with
    | rest, `NUM :: input -> pr 14 rest input Shift; parse_10 ((`NUM, 14) :: rest) input
    | rest, `LPAREN :: input -> pr 14 rest input Shift; parse_13 ((`LPAREN, 14) :: rest) input
    | _, (`MINUS|`RPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"

  and parse_15 rest input =
    match rest, input with
    | _ :: _ :: (_, 1) :: rest, (`MINUS|`RPAREN) :: _ -> pr 15 rest input (Reduce 2); parse_4 ((`E, 1) :: rest) input
    | _ :: _ :: (_, 6) :: rest, (`MINUS|`RPAREN) :: _ -> pr 15 rest input (Reduce 2); parse_11 ((`E, 6) :: rest) input
    | _ :: _ :: (_, 13) :: rest, (`MINUS|`RPAREN) :: _ -> pr 15 rest input (Reduce 2); parse_16 ((`E, 13) :: rest) input
    | _, (`NUM|`LPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_16 rest input =
    match rest, input with
    | rest, `MINUS :: input -> pr 16 rest input Shift; parse_14 ((`MINUS, 16) :: rest) input
    | rest, `RPAREN :: input -> pr 16 rest input Shift; parse_17 ((`RPAREN, 16) :: rest) input
    | _, (`NUM|`LPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"

  and parse_17 rest input =
    match rest, input with
    | _ :: _ :: (_, 1) :: rest, (`MINUS|`RPAREN) :: _ -> pr 17 rest input (Reduce 5); parse_2 ((`T, 1) :: rest) input
    | _ :: _ :: (_, 6) :: rest, (`MINUS|`RPAREN) :: _ -> pr 17 rest input (Reduce 5); parse_9 ((`T, 6) :: rest) input
    | _ :: _ :: (_, 7) :: rest, (`MINUS|`RPAREN) :: _ -> pr 17 rest input (Reduce 5); parse_8 ((`T, 7) :: rest) input
    | _ :: _ :: (_, 13) :: rest, (`MINUS|`RPAREN) :: _ -> pr 17 rest input (Reduce 5); parse_9 ((`T, 13) :: rest) input
    | _ :: _ :: (_, 14) :: rest, (`MINUS|`RPAREN) :: _ -> pr 17 rest input (Reduce 5); parse_15 ((`T, 14) :: rest) input
    | _, (`NUM|`LPAREN|`EOF) :: _ -> failwith "parse error"
    | _, [] -> Printf.kprintf failwith "unexpected EOF"
    | _, tok :: _ -> Printf.kprintf failwith "error %s" (string_of_terminal tok)

  and parse_accept rest input =
    ()

end
