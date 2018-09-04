(** Bloom Filters for Approximate Sets. 

  The implementation is geared towards efficiency at the risk of
  potentially larger false positive rates for membership queries. It
  uses fixed sized bit array that fit into OCaml's int values. So the
  implementation is platform-dependant.

*)

(** The type of approximate sets. *)
type 'a t

(** The empty set. *)
val empty: 'a t

(** Create the singleton approximate set from given element. *)
val singleton: 'a -> 'a t
    
(** Insert element into an approximate set. *)    
val add: 'a -> 'a t -> 'a t

(** Compute intersection of two approximate sets. *)  
val inter: 'a t -> 'a t -> 'a t

(** Compute union of two approximate sets. *)  
val union: 'a t -> 'a t -> 'a t

(** Check whether elemet is contained in an approximate set. *)
val mem: 'a -> 'a t -> bool
