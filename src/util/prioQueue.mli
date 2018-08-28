(** Priority Search Queues.

  Implements the data structure from this paper:
      A Simple Implementation Technique for Priority Search Queues
      Ralf Hinze, ICFP 2001
*)

module type OrderedType = sig
  type t
  val compare: t -> t -> int
end
      
module Make(K: OrderedType)(P: OrderedType): sig

  type t

  val empty: t

  val is_empty: t -> bool
    (* runs in O(1) *)

  val size: t -> int
    (* runs in O(1) *)
      
  val insert: K.t -> P.t -> t -> t
    (* runs in O(log n) *)

  val delete: K.t -> t -> t
    (* runs in O(log n) *)
      
  val min: t -> K.t * P.t
    (* runs in O(1) *)

  val extract_min: t -> K.t * P.t * t
    (* runs in O(log n) *)

  val adjust: (P.t -> P.t) -> K.t -> t -> t
    (* runs in O(log n) *)

  val find_opt: K.t -> t -> P.t option
end
