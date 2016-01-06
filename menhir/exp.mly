%token EOF
%token ADD
%token MUL
%token LPAREN
%token RPAREN
%token<string> ID

%start <T.exp> s

%%
s: e EOF { $1 }

e:
  | e ADD t         { T.Add ($1, $3) }
  | t               { $1 }

t:
  | t MUL f         { T.Mul ($1, $3) }
  | f               { $1 }

f:
  | LPAREN e RPAREN { $2 }
  | ID              { T.Id $1 }
