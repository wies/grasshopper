open Util
open Lexing
open SplSyntax


(** Function to print debug info easily *)
let print_debug str = Debug.info (fun () -> ("\027[1;31mLOCUST: " ^ str ^ "\027[0m\n"))


(** These lists of strings store the filenames for the samples *)
let pos_model_count = ref 0
let neg_model_count = ref 0
let filename_prefix = ref ""
let loop_pos = ref GrassUtil.dummy_position


(** Use this to get the filename for the [n]th ([is_pos] ? positive : negative) model *)
let get_model_filename is_pos n =
  if is_pos
  then (!filename_prefix ^ "_model_pos_" ^ (string_of_int n))
  else (!filename_prefix ^ "_model_neg_" ^ (string_of_int n))


(** Use this to get the filename for a new ([is_pos] ? positive : negative) model *)
let get_new_model_filename is_pos =
  if is_pos
  then begin
      pos_model_count := !pos_model_count + 1;
      (!filename_prefix ^ "_model_pos_" ^ (string_of_int !pos_model_count))
    end
  else begin
      neg_model_count := !neg_model_count + 1;
      (!filename_prefix ^ "_model_neg_" ^ (string_of_int !neg_model_count))
    end


let find_src_pos_of_loop spl_prog proc_name =
  let proc = try
      Grass.IdMap.find proc_name spl_prog.proc_decls
    with
      Not_found -> failwith ("Couldn't find the procedure " ^ (fst proc_name))
  in
  let rec find_loop_pos_in_stmt_list = function
    | Loop (_, _, _, _, pp) :: _ -> pp
    | If (_, stmt1, stmt2, _) :: stmts ->
       (try
	  find_loop_pos_in_stmt stmt1
	with
	  _ -> try
	      find_loop_pos_in_stmt stmt2
	  with
	    _ -> find_loop_pos_in_stmt_list stmts)
    | Block (stmts1, _) :: stmts2 ->
       (try
	  find_loop_pos_in_stmt_list stmts1
	with
	  _ -> find_loop_pos_in_stmt_list stmts2)
    | _ :: stmts -> find_loop_pos_in_stmt_list stmts
    | [] -> failwith ("There is no loop in procedure " ^ (fst proc_name))
  and find_loop_pos_in_stmt = function
    | Loop (_, _, _, _, pp) -> pp
    | If (_, stmt1, stmt2, _) ->
       (try
	  find_loop_pos_in_stmt stmt1
	with
	  _ ->
	  find_loop_pos_in_stmt stmt2)
    | Block (stmts, _) -> find_loop_pos_in_stmt_list stmts
    | _ -> failwith ("There is no loop in procedure " ^ (fst proc_name))
  in
  find_loop_pos_in_stmt proc.p_body
  (* TODO this has the horrible assumption that there is only one loop and that the failing trace included this loop. *)


(** Initialise all refs for a round of invariant finding. *)
let init_refs spl_prog proc =
  Random.self_init ();
  filename_prefix := string_of_int (Random.int 100);
  loop_pos := find_src_pos_of_loop spl_prog proc.Prog.proc_name;
  print_debug ("init_refs set filename_prefix to " ^ !filename_prefix
	       ^ " and loop pos is:\n  " ^ (Grass.string_of_src_pos !loop_pos))


(** Given a Prog.program [prog] and a Prog.proc_decl [proc] with a counter-example
    Model.model [model] for a failed VC at position [pp], find the model as it would 
    appear at position [pos] *)
let get_model_at_src_pos prog proc (pp, model) pos =
  let trace = Verifier.get_trace prog proc (pp, model) in
  (* Return the first (p, model) such that p >= pos *)
  let rec get_first_model_after_pos pos = function
    | (p, model) :: rest_of_trace ->
       if p.Grass.sp_start_line < pos.Grass.sp_start_line
       then get_first_model_after_pos pos rest_of_trace
       else
	 begin
	   print_debug ("got model at line number "
			^ (string_of_int p.Grass.sp_start_line));
	   model
	 end
    | _ -> failwith ("get_model_at_src_pos: no model at position "
		     ^ Grass.string_of_src_pos pos)
  in
  get_first_model_after_pos pos trace


(** Take a heap model as input *)
let read_heap_from_chan chan =
  let lexbuf = Lexing.from_channel chan in
  ModelParser.heap ModelLexer.token lexbuf


let add_model_to_prog (store, heap) prog =
  let pos = GrassUtil.dummy_position in
  let node_typ = StructType ("Node", 0) in
  let mk_ident name = Ident ((name, 0), pos) in
  let mk_ident_from_id id =
    if id <> 0 then
      mk_ident ("n_" ^ (string_of_int id))
    else
      Null (node_typ, pos)
  in
  (* Go through heap and find all heap locations as a set of ids *)
  let node_ids =
    let add_ids_to_set id_set (n1, fld, n2) =
      IntSet.add n1 (IntSet.add n2 id_set)
    in
    List.fold_left add_ids_to_set IntSet.empty heap
  in
  let node_ids = IntSet.remove 0 node_ids in  (* ignore null! *)
  let expr_list = [] in
  (* For each heap location id x, add "acc(n_x)" *)
  let expr_list =
    let add_var_from_id id var_list =
      ProcCall (("acc", 0), [mk_ident_from_id id], pos)
      :: var_list
    in
    IntSet.fold add_var_from_id node_ids expr_list
  in
  (* For each named heap location in the store add "name == n_x" *)
  let expr_list =
    let add_one_var var_list (name, loc_id) =
      BinaryOp (mk_ident name,
  		OpEq,
  		mk_ident_from_id loc_id,
  		BoolType,
  		pos)
      :: var_list
    in
    List.fold_left add_one_var expr_list store
  in
  (* Now for each field edge (id1, fld, id2), add "n_id1.fld == n_id2" *)
  let expr_list =
    let add_one_edge edge_list (id1, fld, id2) =
      if id1 <> 0 then
  	BinaryOp (Read(mk_ident fld, mk_ident_from_id id1, pos),
  		  OpEq,
  		  mk_ident_from_id id2,
  		  BoolType,
  		  pos)
  	:: edge_list
      else
  	edge_list  (* ignore null.next = null *)
    in
    List.fold_left add_one_edge expr_list heap
  in
  (* The precondition describes the model exactly *)
  let requires =
    let add_one_clause expr clause =
      BinaryOp (clause, OpSepStar, expr, BoolType, pos)
    in
    Requires (List.fold_left add_one_clause (Emp pos) expr_list, false)
  in
  
  (* The assertion is the post-condition *)
  let assert_expr =
    let lexbuf = Lexing.from_channel (open_in "sl_formula") in
    SplParser.expr SplLexer.token lexbuf
  in
  let ensures = Ensures (assert_expr, false) in

  (* Collect all idents and add them as formal parameters *)
  let formals =
    let formals =
      IntSet.fold (fun id lst -> ("n_" ^ (string_of_int id), 0) :: lst) node_ids []
    in
    List.fold_left (fun lst (name, _) -> (name, 0) :: lst) formals store
  in

  let locals =
    let mk_var name =
      { v_name = (name, 0);
	v_type = node_typ;
	v_ghost = false;
	v_implicit = false;
	v_aux = false;
	v_pos = pos;
	v_scope = GrassUtil.global_scope; (* TODO is this right?? *)
      }
    in
    let locals =
      let add_one_var id map =
	let name = "n_" ^ (string_of_int id) in
	Grass.IdMap.add (name, 0) (mk_var name) map
      in
      IntSet.fold add_one_var node_ids Grass.IdMap.empty
    in
    List.fold_left
      (fun map (name, _) -> Grass.IdMap.add (name, 0) (mk_var name) map)
      locals store
  in

  (* add this procedure to the program and return*)
  let dummy_proc_decl =
    ProcDecl (
	{
	  p_name = ("dummy_proc", 0);
	  p_formals = formals;
	  p_returns = [];
	  p_locals = locals;
	  p_contracts = [requires; ensures];
	  p_body = Block ([], pos);
	  p_pos = pos;
	})
  in
  SplSyntax.extend_spl_program [] [dummy_proc_decl] prog


(** Check if a procedure is an auto-created loop procedure *)
let is_auto_loop_proc proc =
  Str.string_match (Str.regexp ".*_loop$") (Grass.string_of_ident proc.Prog.proc_name) 0
