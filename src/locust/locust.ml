open Util
open Lexing
open SplSyntax


(** Function to print debug info easily *)
let print_debug str = Debug.info (fun () -> ("\027[1;31mLOCUST: " ^ str ^ "\027[0m\n"))


(** These lists of strings store the filenames for the samples *)
let pos_model_count = ref 0
let neg_model_count = ref 0
let impl_model_count = ref 0
let filename_prefix = ref ""
let loop_pos = ref GrassUtil.dummy_position
let proc_name = ref ("", 0)


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


(** Use this to get the filename for the [n]th implication model *)
let get_impl_model_filename n =
  (!filename_prefix ^ "_model_impl_" ^ (string_of_int n))


(** Use this to get the filename for a new ([is_pos] ? positive : negative) model *)
let get_new_impl_model_filename () =
  impl_model_count := !impl_model_count + 1;
  (!filename_prefix ^ "_model_impl_" ^ (string_of_int !impl_model_count))


(** Check if a procedure is an auto-created loop procedure *)
let is_auto_loop_proc proc_ident =
  Str.string_match (Str.regexp ".*_loop$") (Grass.string_of_ident proc_ident) 0


let find_src_pos_of_loop spl_prog =
  let proc =
    let proc =
      Grass.IdMap.fold (fun key value proc_opt ->
			match proc_opt with
			| Some proc -> Some proc
			| None -> if is_auto_loop_proc key then None else Some value)
		       spl_prog.proc_decls None
    in
    match proc with
    | Some p -> p
    | None -> failwith ("Couldn't find a procedure to run on.")
  in
  proc_name := proc.p_name;
  print_debug ("Starting on procedure "
		      ^ (Grass.string_of_ident proc.p_name));

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
    | [] -> failwith ("There is no loop in procedure " ^ (fst proc.p_name))
  and find_loop_pos_in_stmt = function
    | Loop (_, _, _, _, pp) -> pp
    | If (_, stmt1, stmt2, _) ->
       (try
	  find_loop_pos_in_stmt stmt1
	with
	  _ ->
	  find_loop_pos_in_stmt stmt2)
    | Block (stmts, _) -> find_loop_pos_in_stmt_list stmts
    | _ -> failwith ("There is no loop in procedure " ^ (fst proc.p_name))
  in
  find_loop_pos_in_stmt proc.p_body
  (* TODO this has the horrible assumption that there is only one loop and that the failing trace included this loop. *)


(** Initialise all refs for a round of invariant finding. *)
let init_refs spl_prog =
  Random.self_init ();
  (* filename_prefix := string_of_int (Random.int 100); *)
  loop_pos := find_src_pos_of_loop spl_prog;
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


let add_model_and_assertion_to_prog (store, heap) assert_expr prog =
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
  (* let assert_expr = *)
  (*   let lexbuf = Lexing.from_channel (open_in "sl_formula") in *)
  (*   SplParser.expr SplLexer.token lexbuf *)
  (* in *)
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
  let dummy_proc_name = ("dummy_proc", 0) in
  let dummy_proc_decl =
    ProcDecl (
	{
	  p_name = dummy_proc_name;
	  p_formals = formals;
	  p_returns = [];
	  p_locals = locals;
	  p_contracts = [requires; ensures];
	  p_body = Block ([], pos);
	  p_pos = pos;
	})
  in
  SplSyntax.extend_spl_program [] [dummy_proc_decl] prog, dummy_proc_name


let get_candidates_from_predictor () =
  let base_cmd = "../Source/Repos/FMML/bin/Debug/FMML.exe --variable-number 3 --ds-nest-level 0 --prediction-number 5 --data-dir ../Source/Repos/FMML/data/ --predict-daikon-state " in
  let model_filenames =
    let rec create_str num =
      if num == 0 then ""
      else (get_model_filename true num) ^ " " ^ (create_str (num - 1))
    in
    create_str !pos_model_count
  in
  print_debug ("Calling predictor on files: " ^ model_filenames);
  let cmd = base_cmd ^ model_filenames in
  let in_chan = Unix.open_process_in cmd in

  let candidate_invariants =
    let lexbuf = Lexing.from_channel in_chan in
    SlParser.formulae SlLexer.token lexbuf
  in
  candidate_invariants


(** Main entry point of the learning process
TODO make sure I need all these parameters *)
let learn_invariant spl_prog simple_prog proc errors =
  let process_error (error_pos, error_msg, model) =
    let error_msg = List.hd (Str.split (Str.regexp "\n") error_msg) in
    print_debug ("Found error on line "
			^ (string_of_int error_pos.Grass.sp_start_line)
			^ ": " ^ error_msg);
    (* If error is inside loop body? *)
    if is_auto_loop_proc proc.Prog.proc_name
    then begin
	if Str.string_match (Str.regexp ".*invariant might not be maintained.*") error_msg 0
	then
	  begin
	    (* Implication counter-example *)
	    print_debug "Getting implication model pair";
	    let model1 =
	      get_model_at_src_pos simple_prog proc (error_pos, model)
				   {!loop_pos with
		Grass.sp_start_line = !loop_pos.Grass.sp_start_line + 1}
	    in
	    let model2 = model in
	    let out_filename = get_new_impl_model_filename () in
	    let out_chan = open_out (out_filename ^ "a") in
	    Model.output_txt out_chan model1;
	    close_out out_chan;
	    let out_chan = open_out (out_filename ^ "b") in
	    Model.output_txt out_chan model2;
	    close_out out_chan;
	    print_debug ("Dumped models in files " ^ out_filename ^ "a and " ^ out_filename ^ "b");
	  end
	else
	  begin
	    print_debug "Getting negative model from inside loop";
	    let neg_model =
	      get_model_at_src_pos simple_prog proc (error_pos, model) !loop_pos
	    in
	    let out_filename = get_new_model_filename false in
	    let out_chan = open_out out_filename in
	    Model.output_txt out_chan neg_model;
	    close_out out_chan;
	    print_debug ("Dumped model in file " ^ out_filename);
	  end
      end
    else
      if error_pos.Grass.sp_start_line <= !loop_pos.Grass.sp_start_line
      then
	begin
	  (* Assuming precondition =/> invariant. get positive model *)
	  print_debug "Getting positive model";
	  (* TODO need session or something to get multiple models *)
	  (* TODO what format to get the model in? TODO store models in ref *)
	  (* For now dumping model to file and storing filename in ref *)
	  let out_filename = get_new_model_filename true in
	  let out_chan = open_out out_filename in
	  Model.output_txt out_chan model;
	  close_out out_chan;
	  print_debug ("Dumped model in file " ^ out_filename);
	end
      else
	begin
	  (* Error occured after loop, get negative model *)
	  print_debug "Geting negative model";
	  let neg_model =
	    get_model_at_src_pos
	      simple_prog proc (error_pos, model)
	      {!loop_pos with
		Grass.sp_start_line = !loop_pos.Grass.sp_start_line + 1}
	  in
	  let out_filename = get_new_model_filename false in
	  let out_chan = open_out out_filename in
	  Model.output_txt out_chan neg_model;
	  close_out out_chan;
	  print_debug ("Dumped model in file " ^ out_filename);
	end
    (* TODO what to do if it's not inductive *)
  in
  process_error (List.hd errors)
  (* TODO fix model bug and do this instead: List.iter process_error errors *)

let rec formula_contains_tree_pred = function
  | PredApp (("tree", _), _, _) -> true
  | ProcCall (("tree", _), _, _) -> true
  | BinaryOp (e1, _, e2, _, _) -> formula_contains_tree_pred e1
				  || formula_contains_tree_pred e2
  | _ -> false


let insert_invariant_into_spl_prog spl_prog proc_name inv =
  let proc = try
      Grass.IdMap.find proc_name spl_prog.proc_decls
    with
      Not_found -> failwith ("Couldn't find the procedure " ^ (fst proc_name))
  in
  (* TODO horrible assumption: only one loop! *)
  let rec insert_inv_in_stmt inv = function
    | Block (stmt_list, pos) -> Block (insert_inv_in_stmt_list inv stmt_list, pos)
    | If (e, stmt1, stmt2, pos) -> If (e, insert_inv_in_stmt inv stmt1,
				       insert_inv_in_stmt inv stmt2, pos)
    | Loop (contr, stmt1, e, stmt2, pos) ->
       Loop ([Invariant (inv, false)], stmt1, e, stmt2, pos)
    | s -> s
  and insert_inv_in_stmt_list inv = function
    | st :: stmt_list ->
       (insert_inv_in_stmt inv st) :: (insert_inv_in_stmt_list inv stmt_list)
    | [] -> []
  in
  let proc = {proc with p_body = insert_inv_in_stmt inv proc.p_body} in
  {spl_prog with proc_decls = Grass.IdMap.add proc_name proc spl_prog.proc_decls}


let check_cand_inv_against_models cand assert_model_function =
  let rec verify_on_positives i =
    if i > !pos_model_count then true
    else begin
	print_debug ("Trying on positive model " ^ (string_of_int i));
	if assert_model_function cand (get_model_filename true i) then
	  begin
	    print_debug "Yep."; verify_on_positives (i + 1)
	  end
	else
	  begin
	    print_debug "Nope."; false
	  end
      end
  in
  let rec verify_on_negatives i =
    if i > !neg_model_count then true
    else begin
	print_debug ("Trying on negative model " ^ (string_of_int i));
	if not (assert_model_function cand (get_model_filename false i)) then
	  begin
	    print_debug "Yep."; verify_on_negatives (i + 1)
	  end
	else
	  begin
	    print_debug "Nope."; false
	  end
      end
  in
  let rec verify_on_implications i =
    if i > !impl_model_count then true
    else begin
	print_debug ("Trying on implication model " ^ (string_of_int i));
	if assert_model_function cand ((get_impl_model_filename i) ^ "a") then
	  if assert_model_function cand ((get_impl_model_filename i) ^ "b") then
	    begin
	      print_debug "Yep."; verify_on_implications (i + 1)
	    end
	  else
	    begin
	      print_debug "Nope."; false
	    end
	else
	  begin
	    print_debug "No, so skipping."; verify_on_implications (i + 1)
	  end
      end
  in
  (verify_on_positives 1) && (verify_on_negatives 1) && (verify_on_implications 1)
