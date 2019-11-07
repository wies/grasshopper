(** {5 Symbolic execution based verifier V2} *)

open Util
open Grass
open GrassUtil
open Prog
open Printf

(** symbolic store maintains a mapping from grasshopper vars to symbolic vars
  ident -> ident. *)
type symb_store = ident IdMap.t
let empty_store = IdMap.empty

(** path condition (pc) stack
  A sequence of scopes a tuple of (identifier of pc, scope identifier V, set[V])
  TODO: not clear on how to create identifiers for the pc and the scope identifier.
 *)
type pc_stack = (ident * ident * IdSet.t) list

(** heap elements and symbolic heap
  The symbolic maintains a multiset of heap chunks which are
  of the form (obj, V, [Id -> V]).
  *)
type hc_label = Ref | Acc | Field
type heap_chunk = hc_label * ident * ident IdMap.t

module HCSet = Set.Make(struct
    type t = heap_chunk
    let compare = compare
  end)

type symb_heap = HCSet.t
let empty_heap = HCSet.empty


(** Symbolic State are records that are manipulated during execution:
  1. symbolic store; a mapping from variable names to symbolic values:w
  2. symbolic heap; records which locations, fields, access predicates are
     accessable along with symbolic values they carry.
  3. path condition stack; this carries all path conditions which are represnented
     as symbolic expressions.
 *)
type symb_state = {
    store: symb_store;
    pc: pc_stack;
    heap: symb_heap;
    old: symb_heap;
  }

let mk_fresh_symb_state =
  {store = empty_store; pc = []; heap = empty_heap; old = empty_heap}

(** Helpers to print state *)
let lineSep = "\n--------------------\n"

let string_of_pcset s =
  s
  |> IdSet.elements
  |> List.map (fun ele -> (string_of_ident ele))
  |> String.concat ", "

let string_of_idmap store =
  IdMap.bindings store
  |> List.map (fun (k, v) -> (string_of_ident k) ^ ":" ^ (string_of_ident v))
  |> String.concat ", "
  |> sprintf "{%s}"

let string_of_pc_stack pc =
  pc
  |> List.map (fun (pc, scope_ident, vars) ->
      "(" ^ (string_of_ident pc) ^ ", " ^ (string_of_ident scope_ident) ^ ", "
      ^ (string_of_pcset vars) ^ ")")
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_hc chunk =
  match chunk with
  | Ref, id, m -> sprintf "(Ref, %s, %s)" (string_of_ident id) (string_of_idmap m)
  | Acc, id, m -> sprintf "(Acc, %s, %s)" (string_of_ident id) (string_of_idmap m)
  | Field, id, m -> sprintf "(Field, %s, %s)" (string_of_ident id) (string_of_idmap m)

let string_of_heap h =
  h |> HCSet.elements
  |> List.map (fun ele -> (string_of_hc ele))
  |> String.concat ", "
  |> sprintf "[%s]"

let string_of_state s =
  let store = string_of_idmap s.store in
  let pc = string_of_pc_stack s.pc in
  let heap = string_of_heap s.heap in
  let old = string_of_heap s.old in
  sprintf "Store: %s\nPCStack: %s\nHeap: %s\nOld: %s" store pc heap old
