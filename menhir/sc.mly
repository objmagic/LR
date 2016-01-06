%token C
%token D

%start <T.s> s

%%
(* There's an end-of-stream conflict here which we're ignoring for now so
   that the automaton matches the version in ASU. *)
s:
  | c c { T.S1 ($1, $2) }

c:
  | C c { T.C1 $2 }
  | D   { T.C2 }
