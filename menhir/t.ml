type e = Eid of string | Nest of e * e

type exp = Add of exp * exp | Mul of exp * exp | Id of string

type s = S1 of c * c and c = C1 of c | C2
