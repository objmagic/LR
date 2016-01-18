(** unary number as Gadt list, with two potential return types *)
type (_, _, _, _) num =
  | Z : ('ret, 'ret, 'ret2, 'ret2) num
  | C : ('a, 'ret, 'a2, 'ret2) num -> ('b -> 'a, 'ret, 'b -> 'a2, 'ret2) num

(** Postpend Gadt list *)
type (_,_) tuple =
  | Zero : ('ret, 'ret) tuple
  | Cons : 'b code * ('a, 'b -> 'ret) tuple -> ('a, 'ret) tuple

(** apply a function to a (reversed) tuple. *)
let rec apply
  : type t ret . t code -> (t, ret) tuple -> ret code =
  fun f -> function
    | Zero -> f
    | Cons (v, args) -> .< .~(apply f args) .~v >.

let (~~) x = C x

(** Given a function (f : arg1 -> arg2 ... -> ret)
    and a function (g : ret -> ret2)
    we generate (fun arg1 ... -> g (f arg1 ...)) of type (arg1 -> arg2 -> .. ret2)

    We build the lambda by counting down. While doing that, we accumulate the reversed tuple.
    When we get to zero, we apply f to the tuple, and g to the result.

    type equivalence :
    t ~ arg1 -> arg2 -> .. argN -> ret
    xt ~ argM -> ... argN -> ret
    xt2 ~ argM -> ... argN -> ret2
*)
let rec gen_apply
  : type t xt ret xt2 ret2.
    (ret -> ret2) code -> t code ->
    (t, xt) tuple ->
    (xt, ret, xt2, ret2) num ->
    xt2 code
  = fun g f acc -> function
    | Z -> .< .~g .~(apply f acc) >.
    | C n -> .< fun x -> .~ (gen_apply g f (Cons (.<x>., acc)) n) >.

(** Shortcut, with the empty tuple as accumulator *)
let make_apply g f n = gen_apply g f Zero n

(** Example *)

let f = .< fun x1 x2 x3 -> x1 + x2 + int_of_float x3 >.

let f' = .<fun g -> .~(make_apply .<g>. f (~~ ~~ ~~ Z))>.

let () = Print_code.print_code Format.std_formatter  f'
