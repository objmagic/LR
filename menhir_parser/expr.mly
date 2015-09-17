%{
%}

/* token */

%token KPlus
%token KStar
%token KLeft
%token KRight
%token <int> INT
%token EOF

/* entry points */

%start <int> calc
%%

calc:
  e EOF {$1}

e:
  | e KPlus  t {$1 + $2}
  | t {$1}

t:
  | t KStar f {$1 * $2}
  | f {$1}

f:
  | KLeft e KRight {$2}
  | INT {$1}

