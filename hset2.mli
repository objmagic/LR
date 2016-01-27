(* A value [(a, b) ordering] records the ordering between a value [l]
   of type [a t] and a value [r] of type [b t] for some type context
   [_ t].
   If [l] and [r] are equal then [a] must also be equal to [b];
   otherwise, there are no constraints on the types. *)

module type SetOrderedType2 =
sig
  type ('a, 'b) t
  val compare : ('a, 'b) t -> ('c, 'd) t -> ('e, 'e) Ordering.ordering
end

module type S =
  sig
    type (_, _) elem
    type t
    type iter = {iter:'a 'b. ('a, 'b) elem -> unit}
    type 'b fold = {fold:'a 'c. ('a, 'c) elem -> 'b -> 'b}
    val empty : t
    val is_empty : t -> bool
    val singleton : ('a, 'b) elem -> t
    val compare : t -> t -> int
    val mem : ('a, 'b) elem -> t -> bool
    val add : ('a, 'b) elem -> t -> t
    val union : t -> t -> t
    val cardinal : t -> int
    val iter : iter -> t -> unit
    val fold : 'a fold -> t -> 'a -> 'a
  end

module Make (Ord : SetOrderedType2)
  : S with type ('a, 'b) elem = ('a, 'b) Ord.t
