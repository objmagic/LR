(* A value [(a, b) ordering] records the ordering between a value [l]
   of type [a t] and a value [r] of type [b t] for some type context
   [_ t].
   If [l] and [r] are equal then [a] must also be equal to [b];
   otherwise, there are no constraints on the types. *)

module type SetOrderedType =
sig
  type 'a t
  val compare : 'a t -> 'b t -> ('a, 'b) Ordering.ordering
end

module type S =
  sig
    type _ elem
    type t
    type iter = {iter:'a. 'a elem -> unit}
    type 'b fold = {fold:'a. 'a elem -> 'b -> 'b}
    val empty : t
    val is_empty : t -> bool
    val compare : t -> t -> int
    val mem : 'a elem -> t -> bool
    val add : 'a elem -> t -> t
    val union : t -> t -> t
    val cardinal : t -> int
    val iter : iter -> t -> unit
    val fold : 'a fold -> t -> 'a -> 'a
  end

module Make (Ord : SetOrderedType)
  : S with type 'a elem = 'a Ord.t
