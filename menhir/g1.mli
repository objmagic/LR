
(* The type of tokens. *)

type token = 
  | RP
  | LP
  | ID of (string)
  | EOF

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val e1: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (t.e)
