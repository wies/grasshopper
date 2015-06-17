open Util
open Lexing
open SplSyntax

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
