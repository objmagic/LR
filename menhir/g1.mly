%token <string> ID
%token LP
%token EOF
%token RP

%start <t.e> e1

%%
e1:
  | e1 = e EOF {e1}

e:
  | s = ID {t.Eid s}
  | e1 = e LP e2 = e RP {t.Nest (e1, e2)}
