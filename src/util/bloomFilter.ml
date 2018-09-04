(** Bloom Filters for Approximate Sets. 

  The implementation is geared towards efficiency at the risk of
  potentially larger false positive rates for membership queries. It
  uses fixed sized bit arrays that fit into OCaml's int values. So the
  implementation is platform-dependant.

*)

(** The type of approximate sets. *)
type 'a t = int

(** Size of bit array. *)
let max = Sys.int_size

(** Compute hash of [x]. *)
let hash (x: 'a) =
  Hashtbl.hash x

(** Compute hash of [x] with added 'salt' [salt] *)
let hash_with_salt (x: 'a) (salt: int): int =
  hash (salt + hash x)

(** The empty set. *)
let empty: 'a t = 0

(** Compute index of [x] into bit array. *)
let get_index x =
  let rec get_index h salt =
    if h = max then get_index (hash_with_salt x salt) (salt + 1) else h
  in
  get_index (hash x) 1
    
(** Create the singleton approximate from element [x]. *)
let singleton x =
  let index = get_index x in
  1 lsl index
    
(** Insert [x] into approximate set [xs]. *)    
let add (x: 'a) (xs: 'a t) =
  let index = get_index x in
  xs lor (1 lsl index)

(** Compute intersection of approximate sets [xs] and [ys]. *)  
let inter (xs: 'a t) (ys: 'a t) = xs land ys

(** Compute union of approximate sets [xs] and [ys]. *)  
let union (xs: 'a t) (ys: 'a t) = xs lor ys
    
(** Check whether [x] is contained in approximate set [xs]. *)
let mem (x: 'a) (xs: 'a t): bool =
  let index = get_index x in
  xs land (1 lsl index) <> 0
