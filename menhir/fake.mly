%token A
%token B
%token C

%start <string> main

%%
main:
  | exprA A {"A"}
  | exprB B {"B"}

exprA:
  | C {()}

exprB:
  | C {()}
