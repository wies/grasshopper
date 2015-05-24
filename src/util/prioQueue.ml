(** Priority Search Queues.

  Implements the data structure from this paper:
      A Simple Implementation Technique for Priority Search Queues
      Ralf Hinze, ICFP 2001
*)

module type OrderedType = sig
  type t
  val compare: t -> t -> int
end

module Make(K: OrderedType, P: OrderedType) = struct
   type t =
    | Leaf
    | Node of int * K.t * P.t * t * K.t * t

  let empty = Leaf

  let is_empty t = t = Leaf

  let max_key = function
    | Node (_, _, _, _, m, _) -> m
    | Leaf -> raise Not_found
      
  let get_winner = function
    | Node (_, k, p, t, m, Leaf) -> (k, p, t, m)
    | _ -> raise Not_found

  let size = function
    | Leaf -> 0
    | Node (s, _, _, _, _) -> s

  let node k p l m r =
    Node (size l + size r + 1, k, p, l, m, r)
          
  let winner k p t m = node k p t m Leaf

  let singleton k p = winner k p Leaf k

  let get_singleton = function
    | Node (_, k, p, Leaf, _, Leaf) -> Some(k, p)
    | _ -> None
          
  let balance k p l m r =
    let single_left k p l m r =
      match r with
      | Node (_, rk, rp, rl, rm, rr) ->
          if K.compare rk rm <= 0 && P.compare p rp <= 0
          then node k p (node rk rp l m rl) rm rr
          else node rk rp (node k p l m rl) rm rr
      | Leaf -> node k p l m r
    let single_right k p l m r =
      match l with
      | Node (_, lk, lp, ll, lm, lr) ->
          if K.compare lk lm > 0 && P.compare p lp <= 0
          then node k p ll lm (node lk lp l m lr)
          else node lk lp ll lm (node k p l m lr)
      | Leaf -> node k p l m r
    in
    let double_left k p l m r = match r with
    | Node (_, rk, rp, rl, rm, rr) ->
        single_left k p l m (single_left rk rp rl rm rr)
    | Leaf -> node k p l m r
    in
    let double_right k p l m r = match l with
    | Node (_, lk, lp, ll, lm, lr) ->
        single_right k p (single_right lk lp ll lm lr) m r
    | Leaf -> node k p l m r
    in
    let balance_left k p l m r = match r with
    | Node (_, _, _, rl, _, rr)
      if size rl < size rr
      then single_left k p l m r
      else double_left k p l m r
    | Leaf -> node k p l m r
    in
    let balance_right k p l m r = match l with
    | Node (_, _, _, ll, _, lr)
      if size ll < size lr
      then single_right k p l m r
      else double_right k p l m r
    | Leaf -> node k p l m r
    in
    let alpha = 0.22 in
    if size l + size r < 2
    then node k p l m r
    else if float_of_int (size r) > alpha .* float_of_int (size l)
    then balance_left k p l m r
    else if float_of_int (size l) > alpha .* float_of_int (size r)
    then balance_right k p l m r
    else node k p l m r
      
  let play t1 t2 = match t1, t2 with
  | Leaf, t | t, Leaf -> t
  | t1, t2 ->
      let k1, p1, t1, m1 = get_winner t1 in
      let k2, p2, t2, m2 = get_winner t2 in
      if P.compare p1 p2 <= 0
      then winner k1 p1 (balance k2 p2 t1 m1 t2) m2
      else winner k2 p2 (balance k1 p1 t1 m1 t2) m2

  let get_play = function
    | Node (_, k1, p1, Node (_, k2, p2, l, m2, r), m1, Leaf) ->
        if K.compare k2 m2 <= 0
        then winner k2 p2 l m2, winner k1 p1 r m1
        else winner k1 p1 l m2, winner k2 p2 r m1
    | _ -> raise Not_found
          
  let rec insert k p = function 
    | Leaf -> singleton k p
    | t ->
        if size t = 1 then play (singleton k p) t
        else
          let l, r = get_play t in
          if K.compare k (max_key l) <= 0
          then play (insert k p l) r
          else play l (insert k p r)

  let rec delete k = function 
    | Leaf -> Leaf
    | t ->
        if size t = 1 then
          let k2, _ = get_singleton t in
          if K.compare k k2 = 0 then Leaf else t
        else
          let l, r = get_play t in
          if K.compare k (max_key l) <= 0
          then play (delete k l) r
          else play l (delete k r)


  let rec adjust f k = function
    | Leaf -> Leaf
    | t ->
        if size t = 1 then
          let k2, p = get_singleton t in
          if K.compare k k2 = 0 then singleton k (f p) else t
        else
          let l, r = get_play t in
          if K.compare k (max_key l) <= 0
          then play (adjust f k l) r
          else play l (adjust f k r)
        
  let rec second_best t m = match t with
  | Leaf -> t
  | Node (_, k, p, l, m2, r) ->
      if K.compare k m2 <= 0
      then play (winner k p l m2) (second_best r m)
      else play (second_best l m2) (winner k p r m)

  let min = function
    | Leaf -> raise Not_found
    | Node (_, k, p, _, _, _) ->
        k, p
          
  let extract_min t =
    let k, p, l, m = get_winner t in
    k, p, second_best l m
              
end

