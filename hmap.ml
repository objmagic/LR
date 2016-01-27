module type OrderedType =
sig
  type 'a t
  type 'a value
  val compare : 'a t -> 'b t -> ('a, 'b) Ordering.ordering
end

module type S =
sig
  type _ key
  type _ value
  type t
  type iter = {iter: 'a. 'a key -> 'a value -> unit}
  type 'b fold = {fold: 'a. 'a key -> 'a value -> 'b -> 'b}
  val empty : t
  val is_empty : t -> bool
  val mem : _ key -> t -> bool
  val add : 'a key -> 'a value -> t -> t
  val find : 'a key -> t -> 'a value option
  val union : t -> t -> t
  val iter : iter -> t -> unit
  val fold : 'a fold -> t -> 'a -> 'a
end

module Make (Ord: OrderedType)
  : S with type 'a key = 'a Ord.t
       and type 'a value = 'a Ord.value
  =
struct
  type 'a key = 'a Ord.t
  type 'a value = 'a Ord.value

  type box = Box : 'a key * 'a value -> box (* handle scope escaping *)

  (* Borrowed and adapted from OCaml's standard library.  The OCaml
     license (LGPL version 2 with linking exception) applies. *)
  type t =
      Empty
    | Node : t * 'a key * 'a value * t * int -> t

  type iter = {iter: 'a. 'a key -> 'a value -> unit}
  type 'b fold = {fold: 'a. 'a key -> 'a value -> 'b -> 'b}

  let make_box : type a. a key -> a value -> box = fun k v -> Box (k, v)

  let empty = Empty

  let is_empty = function
    | Empty -> true
    | _ -> false

  let height = function
      Empty -> 0
    | Node(_,_,_,_,h) -> h

  let create : 'a. t -> 'a key -> 'a value -> t -> t =
    fun l x d r ->
      let hl = height l and hr = height r in
      Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

  let bal : 'a. t -> 'a key -> 'a value -> t -> t =
    fun l x d r ->
    let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
    let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
    if hl > hr + 2 then begin
      match l with
        Empty -> invalid_arg "Hmap.bal"
      | Node(ll, lv, ld, lr, _) ->
          if height ll >= height lr then
            create ll lv ld (create lr x d r)
          else begin
            match lr with
              Empty -> invalid_arg "Hmap.bal"
            | Node(lrl, lrv, lrd, lrr, _)->
                create (create ll lv ld lrl) lrv lrd (create lrr x d r)
          end
    end else if hr > hl + 2 then begin
      match r with
        Empty -> invalid_arg "Hmap.bal"
      | Node(rl, rv, rd, rr, _) ->
          if height rr >= height rl then
            create (create l x d rl) rv rd rr
          else begin
            match rl with
              Empty -> invalid_arg "Hmap.bal"
            | Node(rll, rlv, rld, rlr, _) ->
                create (create l x d rll) rlv rld (create rlr rv rd rr)
          end
    end else
      Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

  let rec add : type a. a key -> a value -> t -> t =
    fun x data -> function
      Empty ->
        Node(Empty, x, data, Empty, 1)
    | Node(l, v, d, r, h) ->
        match Ord.compare x v with
        | Ordering.EQ ->
          Node(l, x, data, r, h)
        | Ordering.LT ->
          let ll = add x data l in
          bal ll v d r
        | Ordering.GT ->
          let rr = add x data r in
          bal l v d rr

  let rec mem : type a. a key -> t -> bool =
   fun x -> function
      Empty ->
        false
    | Node(l, v, d, r, _) ->
        match Ord.compare x v with
        Ordering.EQ -> true
      | Ordering.LT -> mem x l
      | Ordering.GT -> mem x r

  let rec find : type a. a key -> t -> a value option =
    fun x -> function
      Empty ->
        None
    | Node(l, v, d, r, _) ->
        match Ord.compare x v with
          Ordering.EQ -> Some d
        | Ordering.LT -> find x l
        | Ordering.GT -> find x r

  let singleton : type a. a key -> a value -> t = fun k v ->
      Node (Empty, k, v, Empty, 1)

  let rec add_min_element : type a. a key -> a value -> t -> t =
    fun k v t ->
      match t with
      | Empty -> singleton k v
      | Node (l, k', v', r, h) ->
        bal (add_min_element k v l) k' v' r

  let rec add_max_element : type a. a key -> a value -> t -> t =
    fun k v t ->
      match t with
      | Empty -> singleton k v
      | Node (l, k', v', r, h) ->
        bal l k' v' (add_min_element k v r)

  let rec join l k v r =
    match (l, r) with
    | (Empty, _) -> add_min_element k v r
    | (_, Empty) -> add_max_element k v l
    | Node (ll, lk, lv, lr, lh), Node(rl, rk, rv, rr, rh) ->
      if lh > rh + 2 then bal ll lk lv (join lr k v r) else
      if rh > lh + 2 then bal (join l k v rl) rk rv rr else
        create l k v r

  let rec min_elt = function
    | Empty -> raise Not_found
    | Node (Empty, k, v, r, _) -> make_box k v
    | Node (l, k, v, r, _) -> min_elt l

  let rec max_elt = function
    | Empty -> raise Not_found
    | Node (l, k, v, Empty, _) -> make_box k v
    | Node (l, k, v, r, _) -> max_elt r

  let rec split : type a. a key -> t -> (t * bool * t) = fun k t ->
    match t with
    | Empty -> Empty, false, Empty
    | Node (l, k', v, r, _) -> begin
      match Ord.compare k k' with
      | Ordering.EQ -> l, true, r
      | Ordering.LT ->
        let ll, pres, rl = split k l in
        ll, pres, join rl k' v r
      | Ordering.GT ->
        let lr, pres, rr = split k r in
        join l k' v lr, pres, rr
      end

  let rec union : t -> t -> t = fun t1 t2 ->
    match (t1, t2) with
    | Empty, t2 -> t2
    | t1, Empty -> t1
    | Node (l1, k1, v1, r1, h1), Node (l2, k2, v2, r2, h2) ->
      if h1 >= h2 then
        if h2 = 1 then add k2 v2 t1 else begin
          let (l2, _, r2) = split k1 t2 in
          join (union l1 l2) k1 v1 (union r1 r2)
        end
      else
        if h1 = 1 then add k1 v1 t2 else begin
          let (l1, _, r1) = split k2 t1 in
          join (union l1 l2) k2 v2 (union r1 r2)
        end

  let rec iter it = function
    | Empty -> ()
    | Node (l, k, v, r, _) -> iter it l; it.iter k v; iter it r

  let rec fold fd t acc =
    match t with
    | Empty -> acc
    | Node (l, k, v, r, _) ->
      fold fd r (fd.fold k v (fold fd l acc))

end

