(** {5 Symbolic execution based verifier V2} *)

open Grass

(* symbolic store maintains a mapping ident -> term. *)
type se_store = term IdMap.t

(** path condition (pc) stack 
  A sequence of scopes a tuple of (identifier of pc, scope identifier V, set[V])
  TODO: not clear on how to create identifiers for the pc and the scope identifier. 
 *)
type pc_stack = (ident * term * TermSet.t) list 

(** heap elements and symbolic heap 
  The symbolic maintains a multiset of heap chunks which are
  of the form (obj, V, [Id -> V]).
  *)
type hc_label = Ref | Acc | Field 
type heap_chunk = hc_label * term * term IdMap.t 

module HCSet = Set.Make(struct
    type t = heap_chunk
    let compare = compare
  end)

type symbolic_heap = HCSet.t

(** Symbolic State are records that are manipulated during execution:
  1. symbolic store; a mapping from variable names to symbolic variables
  2. symbolic heap; records which locations, fields, access predicates are 
     accessable along with symbolic values they carry.
  3. path condition stack; this carries all path conditions which are represnented 
     as symbolic expressions.
 *)
type symbolic_state = {
    store: se_store;
    pc: pc_stack;
    heap: symbolic_heap;
    old: symbolic_heap;
  }
