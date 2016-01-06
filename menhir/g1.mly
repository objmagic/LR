%token <string> ID
%token LP
%token EOF
%token RP

%start <T.e> e1

%%
e1:
  | e1 = e EOF {e1}

e:
  | s = ID {T.Eid s}
  | e1 = e LP e2 = e RP {T.Nest (e1, e2)}
