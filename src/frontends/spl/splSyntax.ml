(** SPL abstract syntax. *)

open Form

type idents = ident list

type pos = Prog.source_position

type name = string

type names = name list

type typ =
  | StructType of ident
  | FieldType of ident * typ
  | SetType of typ
  | IntType
  | BoolType
  | NullType
  | UniversalType
  (*| ArrayType of typ*)

type var_decl_id =
  | IdentDecl of ident
  | ArrayDecl of var_decl_id

type op = 
  | OpDiff | OpUn | OpInt 
  | OpMinus | OpPlus | OpMult | OpDiv 
  | OpEq | OpNeq | OpGt | OpLt | OpGeq | OpLeq | OpIn
  | OpPts | OpSep 
  | OpAnd | OpOr | OpNot 

type compilation_unit =
    { package : name option;
      imports : names;
      var_decls : vars;
      struct_decls : structs;
      proc_decls : procs;
      pred_decls : preds;
    }

and decl =
  | VarDecl of var
  | ProcDecl of proc
  | PredDecl of pred
  | StructDecl of struc

and decls = decl list

and proc =
    { p_name : ident;
      p_formals : idents;
      p_returns : idents;
      p_locals : vars;
      p_contracts : proc_contracts;
      p_body : stmt; 
      p_pos : pos;
    }

and procs = proc IdMap.t

and pred =
    { pr_name : ident;
      pr_formals : idents;
      pr_locals : vars;
      pr_body : expr; 
      pr_pos : pos;
    }

and preds = pred IdMap.t

and var =
    { v_name : ident;
      v_type : typ; 
      v_ghost : bool;
      v_implicit : bool;
      v_aux : bool;
      v_pos : pos;
    }

and vars = var IdMap.t

and proc_contract =
  | Requires of expr
  | Ensures of expr

and proc_contracts = proc_contract list

and struc =
    { s_name : ident;
      s_fields : vars;
      s_pos : pos;
    }

and structs = struc IdMap.t

and stmt =
  | Skip of pos
  | Block of stmts * pos
  | LocalVars of var list * pos
  | Assume of expr * pos
  | Assert of expr * pos
  | Assign of exprs * exprs * pos
  | Havoc of exprs * pos
  | Dispose of expr * pos
  | If of expr * stmt * stmt * pos
  | Loop of loop_contracts * stmt * expr * stmt * pos
  | Return of exprs * pos

and stmts = stmt list

and loop_contracts = loop_contract list

and loop_contract = 
  | Invariant of expr

and expr =
  | Null of pos
  | Emp of pos
  | Setenum of typ * exprs * pos
  | IntVal of int * pos
  | BoolVal of bool * pos
  | New of ident * pos
  | Dot of expr * ident * pos
  | ProcCall of ident * exprs * pos
  | PredApp of ident * exprs * pos
  | Access of expr * pos
  | UnaryOp of op * expr * pos
  | BinaryOp of expr * op * expr * pos
  | Ident of ident * pos

and exprs = expr list

let pos_of_expr = function
  | Null p 
  | Emp p 
  | Setenum (_, _, p)
  | IntVal (_, p) 
  | BoolVal (_, p)
  | New (_, p)
  | Dot (_, _, p)
  | Access (_, p)
  | ProcCall (_, _, p)
  | PredApp (_, _, p)
  | UnaryOp (_, _, p)
  | BinaryOp (_, _, _, p)
  | Ident (_, p) -> p
  
let pos_of_stmt = function
  | Skip pos
  | Block (_, pos)
  | LocalVars (_, pos)
  | Assume (_, pos)
  | Assert (_, pos)
  | Assign (_, _, pos)
  | Dispose (_, pos)
  | Havoc (_, pos)
  | If (_, _, _, pos)
  | Loop (_, _, _, _, pos)
  | Return (_, pos) -> pos

let compilation_unit pkg ims decls =
  let check_uniqueness id pos (vdecls, pdecls, prdecls, sdecls) =
    if IdMap.mem id vdecls || IdMap.mem id sdecls || IdMap.mem id pdecls || IdMap.mem id prdecls
    then ProgError.error pos ("redeclaration of identifier " ^ (fst id) ^ ".");
  in
  let vdecls, pdecls, prdecls, sdecls =
    List.fold_left (fun (vdecls, pdecls, prdecls, sdecls as decls) -> function
      | VarDecl decl -> 
          check_uniqueness decl.v_name decl.v_pos decls;
          IdMap.add decl.v_name decl vdecls, pdecls, prdecls, sdecls
      | ProcDecl decl -> 
          check_uniqueness decl.p_name decl.p_pos decls;
          vdecls, IdMap.add decl.p_name decl pdecls, prdecls, sdecls
      | PredDecl decl -> 
          check_uniqueness decl.pr_name decl.pr_pos decls;
          vdecls, pdecls, IdMap.add decl.pr_name decl prdecls, sdecls
      | StructDecl decl -> 
          check_uniqueness decl.s_name decl.s_pos decls;
          vdecls, pdecls, prdecls, IdMap.add decl.s_name decl sdecls)
      (IdMap.empty, IdMap.empty, IdMap.empty, IdMap.empty)
      decls
  in
  { package = pkg; 
    imports = ims; 
    var_decls = vdecls; 
    struct_decls = sdecls; 
    proc_decls = pdecls;
    pred_decls = prdecls;
  }

let proc_decl hdr body =
  { hdr with p_body = body }

let struct_decl sname sfields pos =
  { s_name = sname;  s_fields = sfields; s_pos = pos }

let var_decl vname vtype vghost vimpl vpos =
  { v_name = vname; v_type = vtype; v_ghost = vghost; v_implicit = vimpl; v_aux = false; v_pos = vpos } 


let mk_block pos = function
  | [] -> Skip pos
  | [stmt] -> stmt
  | stmts -> Block (stmts, pos)

(*
let rec stmt_pos stmt =
  match stmt with
  | Block [] -> -1
  | Block stmts -> stmts_pos stmts
  | LocalVar fld -> var_pos fld.f_var
  | LocalClass c -> id_pos c.cl_name
  | Empty -> -1
  | Label (lbl, _) -> id_pos lbl
  | Expr e -> expr_pos e
  | If (e, s1, opt) ->
      let n = expr_pos e in
      if n <> -1 then n
      else
	let n = stmt_pos s1 in
	if n <> -1 then n
	else
	  (match opt with
	  | Some s2 -> stmt_pos s2
	  | None -> -1)
  | Switch (e, sw) ->
      let n = expr_pos e in
      if n <> -1 then n
      else switch_pos sw
  | While (_, e, st) ->
      let n = expr_pos e in
      if n <> -1 then n
      else stmt_pos st
  | Do (st, e) ->
      let n = stmt_pos st in
      if n <> -1 then n
      else expr_pos e
  | For (init, test, update, st) ->
      let n = stmts_pos init in
      if n <> -1 then n
      else
	let n = (match test with Some e -> expr_pos e | None -> -1) in
	if n <> -1 then n
	else stmts_pos (update @ [st])
  | Break opt -> opt_id_pos opt
  | Continue opt -> opt_id_pos opt
  | Return opt ->
      (match opt with Some e -> expr_pos e | None -> -1)
  | Throw e -> expr_pos e
  | Sync (e, st) ->
      let n = expr_pos e in
      if n <> -1 then n
      else stmt_pos st
  | Try (st, catches, Some f) ->
      let n = stmt_pos st in
      if n <> -1 then n
      else
	let n = catches_pos catches in
	if n <> -1 then n
	else stmt_pos f
  | Try (st, catches, None) ->
      let n = stmt_pos st in
      if n <> -1 then n
      else catches_pos catches
  | AnnotationStmt _ -> -1

and stmts_pos list =
  match list with
  | s :: rest ->
      let n = stmt_pos s in
      if n <> -1 then n
      else stmts_pos rest
  | [] -> -1

and expr_stmt_pos e s =
  let n = expr_pos e in
  if n <> -1 then n
  else stmt_pos s

and switch_pos list =
  match list with
  | (cases, stmts) :: rest ->
      let n = cases_pos cases in
      if n <> -1 then n
      else
	let n = stmts_pos stmts in
	if n <> -1 then n
	else switch_pos rest
  | [] -> -1

and cases_pos list =
  match list with
  | Case e :: rest ->
      let n = expr_pos e in
      if n <> -1 then n
      else cases_pos rest
  | Default :: rest -> cases_pos rest
  | [] -> -1

and expr_pos e =
  match e with
  | Literal _ -> -1
  | ClassLiteral t -> type_pos t
  | NewClass (t, _, _, _) -> type_pos t
  | NewQualifiedClass (e, id, _, _) ->
      let n = expr_pos e in
      if n <> -1 then n
      else id_pos id
  | NewArray (t, dims, _, opt, _) ->
      let n = type_pos t in
      if n <> -1 then n
      else
	let n = exprs_pos dims in
	if n <> -1 then n
	else
	  (match opt with
	  | Some init -> init_pos init
	  | None -> -1)
  | Dot (e, id) ->
      let n = expr_pos e in
      if n <> -1 then n
      else id_pos id
  | Call (e, args) ->
      let n = expr_pos e in
      if n <> -1 then n
      else exprs_pos args
  | ArrayAccess (e1, e2) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else expr_pos e2
  | Postfix (e, _) -> expr_pos e
  | Prefix (_, e) -> expr_pos e
  | Cast (t, e) ->
      let n = type_pos t in
      if n <> -1 then n
      else expr_pos e
  | Infix (e1, op, e2) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else expr_pos e2
  | InstanceOf (e, t) ->
      let n = expr_pos e in
      if n <> -1 then n
      else type_pos t
  | Conditional (e1, e2, e3) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else
	let n = expr_pos e2 in
	if n <> -1 then n
	else expr_pos e3
  | Assignment (e1, _, e2) ->
      let n = expr_pos e1 in
      if n <> -1 then n
      else expr_pos e2
  | Name name ->
      id_pos (List.hd name)

and exprs_pos list =
  match list with
  | e :: rest ->
      let n = expr_pos e in
      if n <> -1 then n
      else exprs_pos rest
  | [] -> -1

and init_pos init =
  match init with
  | ExprInit e -> expr_pos e
  | ArrayInit inits -> inits_pos inits

and inits_pos list =
  match list with
  | init :: rest ->
      let n = init_pos init in
      if n <> -1 then n
      else inits_pos rest
  | [] -> -1

and catches_pos list =
  match list with
  | (var, stmt) :: rest ->
      let n = var_pos var in
      if n <> -1 then n
      else
	let n = stmt_pos stmt in
	if n <> -1 then n
	else catches_pos rest
  | [] -> -1

*)
