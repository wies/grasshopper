(** A module that executes spl_prog progams on heap models *)

open SplSyntax

(* For now assuming no procedure calls, so stack is a single frame *)

type state =
    {
      st : stack;
      hp : heap;
      hp_size : int;
    }
 and stack = (string, valu) Hashtbl.t
 and heap = ((int * string), valu) Hashtbl.t
 and valu = int
   (* | ValAddr of address *)
   (* | ValInt of int *)
   (* | ValBool of bool *)
 (* and address = NullAddr | Addr of int *)


let start_state () =
  {
    st = Hashtbl.create 0;
    hp = Hashtbl.create 0;
    hp_size = 0;  (** allowed heap positions are 1, 2 .. hp_size *)
  }


(** Get/Set methods for state *)
let get_stack_value state varname =
  try Hashtbl.find state.st varname
  with
    Not_found -> failwith (varname ^ " is not on the stack.")

let set_stack_value state varname value =
  Hashtbl.replace state.st varname value;
  state

let new_heap_value state =
  state.hp_size + 1, {state with hp_size = state.hp_size + 1}

let get_heap_value state (addr, fname) =
  if addr > state.hp_size || addr < 1 then
    failwith "get_heap_value: called on invalid address."
  else
    Hashtbl.find state.hp (addr, fname)

let set_heap_value state (addr, fname) value =
  if addr > state.hp_size || addr < 1 then
    failwith "set_heap_value: called on invalid address."
  else
    Hashtbl.replace state.hp (addr, fname) value;
  state

(** Pretty printers for state *)
(* let string_of_valu = function *)
(*   | ValAddr (Addr addr) -> "ValAddr " ^ string_of_int addr *)
(*   | ValAddr NullAddr -> "ValAddr NullAddr" *)
(*   | ValInt i -> "ValInt " ^ string_of_int i *)
(*   | ValBool b -> "ValBool " ^ string_of_bool b *)
let string_of_valu = string_of_int

let string_of_stack st =
  Hashtbl.fold (fun varname value out_str -> out_str ^ "\n    " ^ varname ^ " -> " ^ (string_of_valu value)) st "  Stack:"

let string_of_heap hp =
  Hashtbl.fold (fun (addr, fname) value out_str -> out_str ^ "\n    " ^ (string_of_int addr) ^ "." ^ fname ^ " -> " ^ (string_of_valu value)) hp "  Heap:"

let string_of_state state =
  "State:\n" ^ (string_of_stack state.st) ^ "\n" ^ (string_of_heap state.hp)
  ^ "\n  hp_size = " ^ (string_of_int state.hp_size)


(** Util functions for values *)
let int_of_bool = function
  | true -> 1
  | false -> 0

let bool_of_int = function
  | 0 -> false
  | _ -> true


(** Create a state from model file *)
let state_of_model_file file_chan =
  let lexbuf = Lexing.from_channel file_chan in
  let stack_list, heap_list = ModelParser.heap ModelLexer.token lexbuf in
  let state = start_state () in
  (* Create all stack vars *)
  let process_one_var state (varname, value) =
    set_stack_value state varname value
  in
  let state = List.fold_left process_one_var state stack_list in
  (* Set hp_size to correct value. TODO improve this *)
  let max_addr = List.fold_left (fun prev_max (a, _, _) -> max prev_max a) 0 heap_list in
  let rec create_addrs state =
    if state.hp_size >= max_addr then
      state
    else
      let _, state = new_heap_value state in
      create_addrs state
  in
  let state = create_addrs state in
  (* Make all heap entries *)
  let process_one_heap_entry state (addr, fname, value) =
    set_heap_value state (addr, fname) value
  in
  let state = List.fold_left process_one_heap_entry state heap_list in
  Locust.print_debug "After reading in state";
  print_endline (string_of_state state);
  state


(** Evaluate an expr at a given state *)
let rec eval_expr state = function
  | Ident ((varname, _), _) -> get_stack_value state varname, state
  | Read (Ident ((fname, _), _), Ident ((objname, _), _), _) ->
     let addr = get_stack_value state objname in
     get_heap_value state (addr, fname), state

  (* Address valued expressions *)
  | Null (_, _) -> 0, state
  | New (_, _, _) ->
     new_heap_value state

  (* Integer valued expressions *)
  | IntVal (i, _) -> i, state
  | UnaryOp (OpPlus, exp, _) -> eval_expr state exp
  | UnaryOp (OpMinus, exp, _) ->
     let v, state = eval_expr state exp in
     (-v), state

  | BinaryOp (exp1, OpMult, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     (v1 * v2), state
  | BinaryOp (exp1, OpDiv, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     (v1 / v2), state
  | BinaryOp (exp1, OpPlus, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     (v1 + v2), state
  | BinaryOp (exp1, OpMinus, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     (v1 - v2), state

  (* Boolean valued expressions *)
  | BoolVal (b, _) -> int_of_bool b, state
  | UnaryOp (OpNot, exp, _) ->
     let v, state = eval_expr state exp in
     (match v with
      | 0 -> 1, state
      | _ -> 0, state)
  | BinaryOp (exp1, OpLt, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool (v1 < v2), state
  | BinaryOp (exp1, OpGt, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool (v1 > v2), state
  | BinaryOp (exp1, OpLeq, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool (v1 <= v2), state
  | BinaryOp (exp1, OpGeq, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool (v1 >= v2), state
  | BinaryOp (exp1, OpEq, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool (v1 = v2), state
  | BinaryOp (exp1, OpAnd, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool ((bool_of_int v1) && (bool_of_int v2)), state
  | BinaryOp (exp1, OpOr, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool ((bool_of_int v1) || (bool_of_int v2)), state
  | BinaryOp (exp1, OpImpl, exp2, _, _) ->
     let v1, state = eval_expr state exp1 in
     let v2, state = eval_expr state exp2 in
     int_of_bool ((not (bool_of_int v1)) || (bool_of_int v2)), state

  | _ -> failwith "Haven't written code to evaluate this kind of expr."


(** Evaluate statements on a state *)
let declare_vars var_list exprs_opt state =
  match exprs_opt with
  | Some _ -> failwith "Don't support initialization while declaring."
  | None ->
     let declare_one_var state var = set_stack_value state (fst var.v_name) 0 in
     List.fold_left declare_one_var state var_list

let process_assign lhs_exp_list rhs_exp_list state =
  let process_one_assign state (lhs, rhs) =
    match lhs with
    | Ident ((name, _), _) ->
       (* Stack assignment *)
       let rvalue, state = (eval_expr state rhs) in
       let state = set_stack_value state name rvalue in
       state
    | Read (Ident ((fname, _), _), Ident ((objname, _), _), _) ->
       (* Heap assignment *)
       let addr = get_stack_value state objname in
       let rvalue, state = (eval_expr state rhs) in
       let state = set_heap_value state (addr, fname) rvalue in
       state
    | _ -> failwith "Could not recongnize this assignment."
  in
  List.fold_left process_one_assign state (List.combine lhs_exp_list rhs_exp_list)


(* Temp hack to see intermediate states *)
let rec eval_stmts state stmts =
  print_endline (string_of_state state);
  eval_stmts1 state stmts

and eval_stmts1 state = function
  | Skip (_) :: stmts ->
     Locust.print_debug "eval_stmt: Skip";
     eval_stmts state stmts
  | Block (stmts1, _) :: stmts2 ->
     Locust.print_debug "eval_stmt: Block";
     let state = eval_stmts state stmts1 in
     eval_stmts state stmts2
  | LocalVars (var_list, exprs_opt, _) :: stmts ->
     Locust.print_debug "eval_stmt: LocalVars";
     let state = declare_vars var_list exprs_opt state in
     eval_stmts state stmts
  | Assign (lhs_exp_list, rhs_exp_list, _) :: stmts ->
     Locust.print_debug "eval_stmt: Assign";
     let state = process_assign lhs_exp_list rhs_exp_list state in
     eval_stmts state stmts
  | If (cond, then_stmt, else_stmt, _ ) :: stmts ->
     Locust.print_debug "eval_stmt: If";
     let cond_val, state = eval_expr state cond in
     if bool_of_int cond_val then
	eval_stmts state (then_stmt :: stmts)
     else
	eval_stmts state (else_stmt :: stmts)
  | Havoc (exp_list, _) :: stmts ->
     Locust.print_debug "eval_stmt: Havoc";
     let rand_exp_list =
       List.fold_left
	 (fun rand_list _ ->
	  IntVal (((Random.int 1000) - 500), GrassUtil.dummy_position) :: rand_list)
	 [] exp_list
     in
     let state = process_assign exp_list rand_exp_list state in
     eval_stmts state stmts
  | Loop (contracts, prebody, cond, body, pp) :: stmts ->
     Locust.print_debug "eval_stmt: Loop";
     let cond_val, state = eval_expr state cond in
     if bool_of_int cond_val then
       eval_stmts state (body :: (Loop (contracts, prebody, cond, body, pp)) :: stmts)
     else
       eval_stmts state stmts
  (* | Assume (exp, is_pure, pp) :: stmts -> *)
  (*      failwith ("Don't know how to handle assume. " ^ (Grass.string_of_src_pos pp)) *)
  (* | Assert (exp, is_pure, pp) :: stmts -> *)
  (*    if eval_expr exp state then *)
  (*      eval_stmts state stmts *)
  (*    else *)
  (*      failwith ("Assert failed at position " ^ (Grass.string_of_src_pos pp)) *)
  (* | Dispose (exp, _) :: stmts -> *)
  (*    let state = dispose exp state in *)
  (*    eval_stmts state stmts *)
  (* | Return (exp, _) :: stmts -> *)
  (*    (\* TODO I'm ignoring all remaining statements. Correct? *\) *)
  (*    state *)
  | _ :: stmts ->
     print_endline "Warning, interpreter is ignoring a statement.";
     eval_stmts state stmts
  | [] -> state


let evaluate spl_prog =
  (* Find first procedure to run on *)
  let proc_name, proc = Grass.IdMap.min_binding spl_prog.proc_decls in
  (* let state = start_state () in *)
  let fname = read_line () in
  let in_chan = open_in fname in
  let state = state_of_model_file in_chan in
  close_in in_chan;
  Random.init 4;  (* TODO pass random state with state? *)
  let _ = eval_stmts state [proc.p_body] in
  ()
