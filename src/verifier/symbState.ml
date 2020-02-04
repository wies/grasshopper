(** {5 Symbolic state primitives inspired by Viper's Silicon} *)

open Util
open Grass
open GrassUtil
open Prog
open Printf

exception NotYetImplemented
let todo () = raise NotYetImplemented

(** Symbolic values; grasshopper distinguishes between terms and forms,
  viper's silicon doesn't *)
type symb_val = 
  | Term of term
  | Form of form

let mk_fresh_symb_val srt prefix = 
  Term (mk_fresh_var srt prefix)

(** Symbolic store:
  maintains a mapping from grasshopper vars to symbolic vals
  ident -> symb_val . *)
(* Note: adding sort so we can remember type when we sub in symbolic vals *)
type symb_store = symb_val IdMap.t
let empty_store = IdMap.empty

let merge_symb_stores g1 g2 =
  IdMap.merge
  (fun x oy oz -> match oy, oz with
  | Some y, Some z -> 
      failwith "todo: figure out how to merge symb_store variables"
  | Some y, None -> Some y
  | None, Some z -> Some z
  | None, None -> None) g1 g2

let find_symb_val store id =
  Debug.debug(
    fun () ->
      sprintf "trying to find symbv for identifier %s\n"
      (string_of_ident id)
  );
  try IdMap.find id store
  with Not_found ->
    failwith ("find_symb_val: Could not find symbolic val for " ^ (string_of_ident id))

(** havoc a list of terms into a symbolic store *)
let mk_fresh_term label srt =
  Term (mk_fresh_var srt label)

let havoc_terms symb_store terms =
  List.fold_left
    (fun sm term ->
      match term with
      | App (_, _, _) -> failwith "tried to havoc a term that isn't a Var"
      | Var (id, srt) -> IdMap.add id (mk_fresh_term "v" srt) sm)
    symb_store terms

(** path condition (pc) stack
  A sequence of scopes a tuple of (scope id, branch condition, [V])
  list[V] is the list of path conditions.
  Note: scope identifiers are used to label branche conditions
    and path conds obtained from two points of program execution.
 *)

(** path condition chunks are of shape (scope id, branch cond, pc list)
 TODO: optimize symb_val list to use a set. *)
type pc_stack = (ident * symb_val * symb_val list) list

let pc_push_new (stack: pc_stack) scope_id br_cond =
  match stack with
  | [] -> [(scope_id, br_cond, [])]
  | stack -> (scope_id, br_cond, []) :: stack

let rec pc_add_path_cond (stack: pc_stack) pc_val =
  match stack with
  | [] -> 
      pc_add_path_cond (pc_push_new stack ("scopeId", 0)
        (mk_fresh_symb_val Bool "brcond")) pc_val 
  | (sid, bc, pcs) :: stack' -> (sid, bc, pc_val :: pcs) :: stack'

let rec pc_after pc_stack scope_id =
  match pc_stack with
  | [] -> []
  | (sid, bc, pcs) :: stack' ->
    if sid = scope_id
    then (sid, bc, pcs) :: pc_after stack' scope_id
    else pc_after stack' scope_id

let pc_collect_constr (stack: pc_stack) =
  List.fold_left
  (fun pclist (id, bc, pcs) -> bc :: (pcs @ pclist))
  [] stack

(** Snapshot defintions *)
type snap =
  | Unit 
  | Snap of symb_val
  | SnapPair of snap * snap 

let snap_pair s1 s2 = SnapPair (s1, s2)

let snap_first s =
  match s with
  | Unit -> Unit
  | Snap s -> Snap s
  | SnapPair (s1, s2) -> s1

let snap_second s =
  match s with
  | Unit -> Unit
  | Snap s -> Snap s
  | SnapPair (s1, s2) -> s2

let mk_fresh_snap srt = 
  Snap (Term (mk_fresh_var srt "snap"))

let term_of_snap = function
  | Unit -> Var (("unit", 0), Bool)
  | Snap (Term t) -> t
  | Snap (Form f) -> todo()
  | SnapPair (_, _) -> todo()

(** snapshot adt encoding for SMT solver *)
let snap_adt = (("snap_tree", 0),
  [(("emp", 0), []);
   (("tree", 0),
    [(("fst", 0), FreeSrt ("snap_tree", 0));
     (("snd", 0), FreeSrt ("snap_tree", 0))
    ])
  ])

let snap_typ = Adt (("snap_tree", 0), [snap_adt])

(** heap elements and symbolic heap
  The symbolic maintains a multiset of heap chunks which are
  of the form obj(symb_val, snap, [Id -> V]) or a predicate with an id
  and list of args.
  *)
type heap_chunk =
  | Obj of symb_val * snap * symb_val IdMap.t
  | Pred of ident * symb_val list

type symb_heap = heap_chunk list

let heap_add h stack hc = (hc :: h, stack)

(** TODO: Not sure about q_continue and entailment checking *)
let heap_remove h stack hc q_continue = todo ()

(** Symbolic State are records that are manipulated during execution:
  1. symbolic store; a mapping from variable names to symbolic values
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
    prog: program; (* need to carry around prog for prover check *)
  }

let mk_symb_state st prog =
  {store=st; pc=[]; heap=[]; old=[]; prog=prog}

let mk_empty_state = 
  {store=empty_store; pc=[]; heap=[]; old=[]; prog=empty_prog}

let update_store state store =
  {state with store=store}
