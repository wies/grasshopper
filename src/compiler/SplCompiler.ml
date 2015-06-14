(** Translation of Abstract Syntax Tree to C program *)

open Util 
open Prog
open Sl
open Grass
open SplSyntax
open SplTypeChecker

let unknown_ident_error id pos =
  ProgError.error pos ("Unknown identifier " ^ GrassUtil.name id ^ ".")

let not_a_struct_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a struct.")

let not_a_proc_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a procedure or predicate.")

let not_a_pred_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a procedure or predicate.")

let not_a_field_error id pos =
  ProgError.error pos 
    ("Identifier " ^ GrassUtil.name id ^ " does not refer to a struct field.")

let redeclaration_error id pos =
  ProgError.error pos ("Identifier " ^ GrassUtil.name id ^ " has already been declared in this scope.")
    
let assignment_mismatch_error pos =
  ProgError.error pos 
    "Mismatch in number of expressions on left and right side of assignment"                

let abstract_initializer_error pos id =
  ProgError.error pos
    ("Unable to infer unique type from initializer of variable " ^ GrassUtil.name id ^ ". Type annotation required.")
    
let null_access_error pos =
  ProgError.error pos "Tried to dereference of access null."

let footprint_declaration_error id pos =
  ProgError.error pos ("Footprint parameter " ^ string_of_ident id ^ " has an unexpected type. Expected type " ^
                       string_of_type (SetType (StructType ("T", 0))) ^ " for some struct type T.")

let invalid_nested_proc_call_error id pos =
  ProgError.error pos 
    ("Procedure " ^ GrassUtil.name id ^ " has more than one return value.")


(** Resolve names of identifiers in compilation unit [cu] so that all identifiers have unique names.*)
let resolve_names cu =
  let lookup_id init_id tbl pos =
    let name = GrassUtil.name init_id in
    match SymbolTbl.find tbl name with
    | Some (id, _) -> id
    | None -> unknown_ident_error init_id pos
  in 
  let check_struct id structs pos =
    if not (IdMap.mem id structs) then
      not_a_struct_error id pos
  in
  let check_proc id procs pos =
    if not (IdMap.mem id procs) then
      not_a_proc_error id pos
  in
  let check_pred id preds pos =
    if not (IdMap.mem id preds) then
      not_a_pred_error id pos
  in
  (*let check_field id globals pos =
    let error () = not_a_field_error id pos in
    try 
      let decl = IdMap.find id globals in
      match decl.v_type with
      | MapType (StructType _, _) -> ()
      | _ -> error ()
    with Not_found -> error ()
  in*)
  let declare_name pos init_id scope tbl =
    let name = GrassUtil.name init_id in
    match SymbolTbl.find_local tbl name with
    | Some _ -> redeclaration_error init_id pos
    | None ->
        let id = GrassUtil.fresh_ident name in
        (id, SymbolTbl.add tbl name (id, scope))
  in
  let declare_var structs decl tbl =
    let id, tbl = declare_name decl.v_pos decl.v_name decl.v_scope tbl in
        let ty = 
          match decl.v_type with
          | StructType init_id ->
              let id = lookup_id init_id tbl decl.v_pos in
              check_struct id structs decl.v_pos;
              StructType id
          | ty -> ty
        in
        { decl with v_name = id; v_type = ty }, tbl
  in
  let declare_vars vars structs tbl = 
    IdMap.fold 
      (fun _ decl (vars, tbl) ->
        let decl, tbl = declare_var structs decl tbl in
        IdMap.add decl.v_name decl vars, tbl)
      vars (IdMap.empty, tbl)
  in
  let tbl = SymbolTbl.empty in
  (* declare struct names *)
  let structs0, tbl =
    IdMap.fold 
      (fun init_id decl (structs, tbl) ->
        let id, tbl = declare_name decl.s_pos init_id GrassUtil.global_scope tbl in
        IdMap.add id { decl with s_name = id } structs, tbl)
      cu.struct_decls (IdMap.empty, tbl)
  in
  (* declare global variables *)
  let globals0, tbl = declare_vars cu.var_decls structs0 tbl in
  (* declare struct fields *)
  let structs, globals, tbl =
    IdMap.fold
      (fun id decl (structs, globals, tbl) ->
        let fields, globals, tbl =
          IdMap.fold 
            (fun init_id fdecl (fields, globals, tbl) ->
              let id, tbl = declare_name fdecl.v_pos init_id GrassUtil.global_scope tbl in
              let res_type = match fdecl.v_type with
              | StructType init_id ->
                  let id = lookup_id init_id tbl fdecl.v_pos in
                  check_struct id structs0 fdecl.v_pos;
                  StructType id
              | ty -> ty
              in
              let typ = MapType (StructType decl.s_name, res_type) in
              let fdecl = { fdecl with v_name = id; v_type = res_type } in
              let gfdecl = { fdecl with v_type = typ } in
              IdMap.add id fdecl fields, IdMap.add id gfdecl globals, tbl
            )
            decl.s_fields (IdMap.empty, globals, tbl)
        in
        IdMap.add id { decl with s_fields = fields } structs, 
        globals, 
        tbl
      )
      structs0 (IdMap.empty, globals0, tbl)
  in
  (* declare procedure names *)
  let procs0, tbl =
    IdMap.fold (fun init_id decl (procs, tbl) ->
      let id, tbl = declare_name decl.p_pos init_id GrassUtil.global_scope tbl in
      IdMap.add id { decl with p_name = id } procs, tbl)
      cu.proc_decls (IdMap.empty, tbl)
  in
  (* declare predicate names *)
  let preds0, tbl =
    IdMap.fold (fun init_id decl (preds, tbl) ->
      let id, tbl = declare_name decl.pr_pos init_id GrassUtil.global_scope tbl in
      IdMap.add id { decl with pr_name = id } preds, tbl)
      cu.pred_decls (IdMap.empty, tbl)
  in
  let cu = 
    { cu with
      var_decls = globals; 
      struct_decls = structs; 
      proc_decls = procs0;
      pred_decls = preds0;
    }
  in
  let resolve_expr locals tbl e =
    let rec re_ty pos tbl = function
      | StructType init_id ->
          let id = lookup_id init_id tbl pos in
          check_struct id structs pos;
          StructType id
      | SetType ty ->
          SetType (re_ty pos tbl ty)
      | ArrayType ty ->
          ArrayType (re_ty pos tbl ty)
      | MapType (dty, rty) ->
          MapType (re_ty pos tbl dty, re_ty pos tbl rty)
      | ty -> ty
    in
    let rec re locals tbl = function
      | Setenum (ty, args, pos) ->
          let ty1 = re_ty pos tbl ty in
          let args1 = List.map (re locals tbl) args in
          Setenum (ty1, args1, pos)
      | New (ty, args, pos) ->
          let ty1 = re_ty pos tbl ty in 
          let args1 =  List.map (re locals tbl) args in
          New (ty1, args1, pos)
      | Read ((Ident (("length", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayType _ -> Length (idx1, pos)
          | ty -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("cells", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayType _ -> ArrayCells (idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("array", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayCellType _ -> ArrayOfCell (idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("index", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayCellType _ -> IndexOfCell (idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read (map, idx, pos) ->
          Read (re locals tbl map, re locals tbl idx, pos)
      | Quant (q, decls, f, pos) ->
          let (decls1, (locals1, tbl1)) = 
            Util.fold_left_map
              (fun (locals, tbl) decl -> match decl with
              | GuardedVar (init_id, e) ->
                let e1 = re locals tbl e in
                let id, tbl1 = declare_name pos init_id pos tbl in
                (GuardedVar (id, e1)), (locals, tbl1) 
              | UnguardedVar decl ->
                let decl, tbl1 = declare_var structs decl tbl in
                (UnguardedVar decl), (IdMap.add decl.v_name decl locals, tbl1)
              )
              (locals, tbl)
              decls
          in
          let f1 = re locals1 tbl1 f in
          Quant (q, decls1, f1, pos)
      | ProcCall (("acc", _ as id), args, pos) ->
          let args1 = List.map (re locals tbl) args in
          (match args1 with
          | [arg] ->
              (match type_of_expr cu locals arg with
              | SetType _ -> 
                  Access (re locals tbl arg, pos)
              | ty ->
                  Access (Setenum (ty, [re locals tbl arg], pos), pos))
          | [map; idx] ->
              (match type_of_expr cu locals map with
              | ArrayType typ ->
                  let map1 = re locals tbl map in
                  let idx1 = re locals tbl idx in
                  let cell = Read (ArrayCells (map1, pos_of_expr map1), idx1, pos) in
                  Access (Setenum (ArrayCellType typ, [cell], pos), pos)
              | _ -> pred_arg_mismatch_error pos id 1)
          | _ -> pred_arg_mismatch_error pos id 1)
      | ProcCall (("Btwn", _ as id), args, pos) ->
          let args1 = List.map (re locals tbl) args in
          (match args1 with
          | [fld; x; y; z] ->
              BtwnPred (fld, x, y, z, pos)
          | _ -> pred_arg_mismatch_error pos id 4)
      | ProcCall (("Reach", _ as id), args, pos) ->
          let args1 = List.map (re locals tbl) args in
          (match args1 with
          | [fld; x; y] ->
              BtwnPred (fld, x, y, y, pos)
          | _ -> pred_arg_mismatch_error pos id 3)
      | ProcCall (init_id, args, pos) ->
          let id = lookup_id init_id tbl pos in
          let args1 = List.map (re locals tbl) args in
          (try 
            check_proc id procs0 pos;
            ProcCall (id, args1, pos)
          with ProgError.Prog_error _ ->
            check_pred id preds0 pos;
            PredApp (id, args1, pos))
      | PredApp (init_id, args, pos) ->
          let id = lookup_id init_id tbl pos in
          check_pred id preds0 pos;
          PredApp (id, List.map (re locals tbl) args, pos)              
      | UnaryOp (op, e, pos) ->
          UnaryOp (op, re locals tbl e, pos)
      | BinaryOp (e1, op, e2, ty, pos) ->
          BinaryOp (re locals tbl e1, op, re locals tbl e2, ty, pos)
      | Ident (init_id, pos) ->
          let id = lookup_id init_id tbl pos in
          Ident (id, pos)
      | Annot (e, GeneratorAnnot (es, ge), pos) ->
          let es1 = List.map (re locals tbl) es in
          Annot (re locals tbl e, GeneratorAnnot (es1, re locals tbl ge), pos)
      | Annot (e, ann, pos) ->
          Annot (re locals tbl e, ann, pos)
      | e -> e
    in
    re locals tbl e
  in
  let rec resolve_stmt locals tbl = function
    | Skip pos -> Skip pos, locals, tbl
    | Block (stmts0, pos) ->
        let stmts, locals, _ = 
          List.fold_left
            (fun (stmts, locals, tbl) stmt0  ->
              let stmt, locals, tbl = resolve_stmt locals tbl stmt0 in
              stmt :: stmts, locals, tbl
            ) 
            ([], locals, SymbolTbl.push tbl) stmts0
        in Block (List.rev stmts, pos), locals, tbl
    | LocalVars (vars, es_opt, pos) ->
        let es_opt1, tys =
          match es_opt with
          | Some es ->
              let es1, tys = 
                Util.map_split (fun e -> 
                    let e1 = resolve_expr locals tbl e in
                    e1, type_of_expr cu locals e1) es
              in
              Some es1, tys
          | None ->
              None, List.map (fun decl -> decl.v_type) vars
        in
        let ids, locals, tbl = 
          try 
            List.fold_right2
              (fun decl ty (ids, locals, tbl) ->
                let decl = 
                  match decl.v_type with
                  | AnyType ->
                      if is_abstract_type ty then
                        abstract_initializer_error pos decl.v_name;
                      { decl with v_type = ty }
                  | _ -> decl
                in
                let decl, tbl = declare_var structs decl tbl in
                Ident (decl.v_name, decl.v_pos) :: ids, 
                IdMap.add decl.v_name decl locals, 
                tbl
              )
              vars tys ([], locals, tbl)
          with Invalid_argument _ -> assignment_mismatch_error pos
        in
        (match es_opt1 with
        | Some es1 -> 
            Assign (ids, es1, pos), locals, tbl
        | None -> 
            Havoc (ids, pos), locals, tbl)
    | Assume (e, pure, pos) ->
        Assume (resolve_expr locals tbl e, pure, pos), locals, tbl
    | Assert (e, pure, pos) ->
        Assert (resolve_expr locals tbl e, pure, pos), locals, tbl
    | Assign (lhs, rhs, pos) ->
        let lhs1 = List.map (resolve_expr locals tbl) lhs in
        let rhs1 = List.map (resolve_expr locals tbl) rhs in
        Assign (lhs1, rhs1, pos), locals, tbl
    | Dispose (e, pos) -> 
        Dispose (resolve_expr locals tbl e, pos), locals, tbl
    | Havoc (es, pos) ->
        let es1 = List.map (resolve_expr locals tbl) es in
        Havoc (es1, pos), locals, tbl
    | If (cond, t, e, pos) ->
        let t1, locals, _ = resolve_stmt locals tbl t in
        let e1, locals, _ = resolve_stmt locals tbl e in
        If (resolve_expr locals tbl cond, t1, e1, pos), locals, tbl
    | Loop (inv, preb, cond, postb, pos) ->
        let inv1 = 
          List.fold_right 
            (function Invariant (e, pure) -> fun inv1 ->
              Invariant (resolve_expr locals tbl e, pure) :: inv1
            ) 
            inv []
        in
        let preb1, locals, _ = resolve_stmt locals tbl preb in
        let cond1 = resolve_expr locals tbl cond in
        let postb1, locals, _ = resolve_stmt locals tbl postb in
        Loop (inv1, preb1, cond1, postb1, pos), locals, tbl
    | Return (es, pos) ->
        Return (List.map (resolve_expr locals tbl) es, pos), locals, tbl
  in
  (* declare and resolve local variables *)
  let procs =
    IdMap.fold
      (fun _ decl procs ->
        let locals0, tbl0 = declare_vars decl.p_locals structs (SymbolTbl.push tbl) in
        let formals = List.map (fun id -> lookup_id id tbl0 decl.p_pos) decl.p_formals in
        let returns = List.map (fun id -> lookup_id id tbl0 decl.p_pos) decl.p_returns in
        let contracts =
          let pre_locals, pre_tbl =
            List.fold_left
              (fun (pre_locals, pre_tbl) id ->
                IdMap.remove id pre_locals,
                SymbolTbl.remove pre_tbl (GrassUtil.name id))
              (locals0, tbl0)
              returns
          in
          List.map 
            (function 
              | Requires (e, pure) -> Requires (resolve_expr pre_locals pre_tbl e, pure)
              | Ensures (e, pure) -> Ensures (resolve_expr locals0 tbl0 e, pure)
            )
            decl.p_contracts
        in
        let body, locals, _ = resolve_stmt locals0 tbl0 decl.p_body in
        let decl1 = 
          { decl with 
            p_formals = formals;
            p_returns = returns;
            p_locals = locals; 
            p_contracts = contracts; 
            p_body = body } 
        in
        IdMap.add decl.p_name decl1 procs
      )
      procs0 IdMap.empty 
  in
  let preds =
    IdMap.fold
      (fun _ decl preds ->
        let locals, tbl = declare_vars decl.pr_locals structs (SymbolTbl.push tbl) in
        let body = resolve_expr locals tbl decl.pr_body in
        let formals = List.map (fun id -> lookup_id id tbl decl.pr_pos) decl.pr_formals in
        let footprints =
          List.map (fun id -> lookup_id id tbl decl.pr_pos) decl.pr_footprints
        in
        let outputs = List.map (fun id -> lookup_id id tbl decl.pr_pos) decl.pr_outputs in
        let decl1 = 
          { decl with 
            pr_formals = formals;
            pr_footprints = footprints;
            pr_outputs = outputs; 
            pr_locals = locals; 
            pr_body = body 
          } 
        in
        IdMap.add decl.pr_name decl1 preds
      )
      preds0 IdMap.empty 
  in
  let bg_theory =
    List.map
      (fun (e, pos) -> resolve_expr globals tbl e, pos)
      cu.background_theory
  in
  { cu with 
    var_decls = globals; 
    struct_decls = structs; 
    proc_decls = procs;
    pred_decls = preds;
    background_theory = bg_theory;
  }

(** Flatten procedure calls and new expressions in compilation unit [cu].*)
let flatten_exprs cu =
  let decl_aux_var name vtype pos scope locals =
    let aux_id = GrassUtil.fresh_ident name in
    let decl = 
      { v_name = aux_id;
        v_type = vtype;
        v_ghost = false;
        v_implicit = false;
        v_aux = true;
        v_pos = pos;
        v_scope = scope;
      }
    in
    let locals1 = IdMap.add aux_id decl locals in
    aux_id, locals1
  in
  let rec check_side_effects = function
    | e -> ()
  in
  let rec flatten_expr scope aux locals = function
    | Setenum (ty, args, pos) as e ->
        List.iter check_side_effects args;
        e, aux, locals
    | New (ty, args, pos) ->
        let aux_id, locals = decl_aux_var "tmp" ty pos scope locals in
        let args1, aux1, locals = 
          List.fold_right 
            (fun arg (args1, aux1, locals) ->
              let arg1, aux1, locals = flatten_expr scope aux1 locals arg in
              arg1 :: args1, aux1, locals
            ) args ([], aux, locals)
        in
        let aux_var = Ident (aux_id, pos) in
        let alloc = Assign ([aux_var], [New (ty, args1, pos)], pos) in
        aux_var, alloc :: aux1, locals
    | Read (map, idx, pos) ->
        let map1, aux1, locals = flatten_expr scope aux locals map in
        let idx1, aux2, locals = flatten_expr scope aux1 locals idx in
        Read (map1, idx1, pos), aux2, locals
    | Quant (q, vars, f, pos) as e ->
        List.iter
          (fun v -> match v with
          | GuardedVar (_,s) -> check_side_effects s
          | _ -> () )
          vars;
        check_side_effects f;
        e, aux, locals
    | ProcCall (id, args, pos) ->
        let pdecl = IdMap.find id cu.proc_decls in
        let res_type = 
          match pdecl.p_returns with
          | [res] ->
              let rdecl = IdMap.find res pdecl.p_locals in
              rdecl.v_type
          | _ -> invalid_nested_proc_call_error pdecl.p_name pos
        in
        let aux_id, locals = decl_aux_var "tmp" res_type pos scope locals in
        let args1, aux1, locals = 
          List.fold_right 
            (fun arg (args1, aux1, locals) ->
              let arg1, aux1, locals = flatten_expr scope aux1 locals arg in
              arg1 :: args1, aux1, locals
            ) args ([], aux, locals)
        in
        let aux_var = Ident (aux_id, pos) in
        let call = Assign ([aux_var], [ProcCall (id, args1, pos)], pos) in
        aux_var, (aux1 @ [call]), locals
    | Access (arg, pos) as e ->
        check_side_effects [arg];
        e, aux, locals
    | BtwnPred (fld, x, y, z, pos) as e ->
        check_side_effects [fld; x; y; z];
        e, aux, locals
    | PredApp (init_id, args, pos) as e->
        List.iter check_side_effects args;
        e, aux, locals
    | UnaryOp (op, e, pos) ->
        let e1, aux1, locals = flatten_expr scope aux locals e in
        UnaryOp (op, e1, pos), aux1, locals
    | BinaryOp (e1, op, e2, ty, pos) ->
        let e21, aux1, locals = flatten_expr scope aux locals e2 in
        let e11, aux2, locals = flatten_expr scope aux1 locals e1 in
        BinaryOp (e11, op, e21, ty, pos), aux2, locals
    | e -> e, aux, locals
  in
  let rec flatten scope locals returns = function
    | Skip pos -> Skip pos, locals
    | Block (stmts0, pos) ->
        let stmts, locals = 
          List.fold_left
            (fun (stmts, locals) stmt0  ->
              let stmt, locals = flatten pos locals returns stmt0 in
              stmt :: stmts, locals
            ) 
            ([], locals) stmts0
        in Block (List.rev stmts, pos), locals
    | LocalVars (_, _, pos) ->
        failwith "flatten_exprs: LocalVars should have been eliminated"
    | (Assume (e, pure, pos) as stmt)
    | (Assert (e, pure, pos) as stmt) ->
        check_side_effects e;
        stmt, locals
    | Assign (lhs, [ProcCall (id, args, cpos)], pos) ->
        let args1, aux1, locals = 
          List.fold_right 
            (fun e (es, aux, locals) ->
              let e1, aux1, locals = flatten_expr scope aux locals e in
              e1 :: es, aux1, locals
            ) 
            args ([], [], locals)
        in 
        let lhs1, aux2, locals = 
          match lhs with
          | [Read (map, idx, opos)] ->
              let res_ty = 
                match type_of_expr cu locals map with
                | MapType (_, ty) -> ty
                | ArrayType ty -> ty
                | ty -> ty
              in
              let aux_id, locals = decl_aux_var "tmp" res_ty opos scope locals in
              let aux_var = Ident (aux_id, pos) in
              let assign_aux, locals =
                flatten scope locals returns (Assign ([Read (map, idx, opos)], [aux_var], pos)) in
              [aux_var], [assign_aux], locals
          | _ ->
              List.fold_right 
                (fun e (es, aux, locals) ->
                  let e1, aux1, locals = flatten_expr scope aux locals e in
                  e1 :: es, aux1, locals
                ) 
                lhs ([], aux1, locals)
        in 
        mk_block pos ([Assign (lhs1, [ProcCall (id, args1, cpos)], pos)] @ aux2), locals
    | Assign (lhs, rhs, pos) ->
        let rhs1, aux1, locals = 
          List.fold_right 
            (fun e (es, aux, locals) ->
              let e1, aux1, locals = flatten_expr scope aux locals e in
              e1 :: es, aux1, locals
            ) 
            rhs ([], [], locals)
        in 
        let lhs1, aux2, locals = 
          List.fold_right 
            (fun e (es, aux, locals) ->
              let e1, aux1, locals = flatten_expr scope aux locals e in
              match e1 with
              | Read(Ident _, _, _) ->
                  e1 :: es, aux1, locals
              | Read (map, ind, opos) ->
                  let mpos = pos_of_expr map in
                  let aux_id, locals =
                    decl_aux_var "tmp" (type_of_expr cu locals map) mpos scope locals
                  in
                  let aux_var = Ident (aux_id, mpos) in
                  let assign_aux = Assign ([aux_var], [map], mpos) in
                  Read (aux_var, ind, opos) :: es, aux1 @ [assign_aux], locals
              | _ ->
                  e1 :: es, aux1, locals
            ) 
            lhs ([], aux1, locals)
        in 
        mk_block pos (aux2 @ [Assign (lhs1, rhs1, pos)]), locals
    | Dispose (e, pos) -> 
        let e1, aux, locals = flatten_expr scope [] locals e in
        mk_block pos (aux @ [Dispose (e1, pos)]), locals
    | Havoc (es, pos) -> 
        let es1, aux1, locals = 
          List.fold_right 
            (fun e (es, aux, locals) ->
              let e1, aux1, locals1 = flatten_expr scope aux locals e in
              e1 :: es, aux1, locals
            ) 
            es ([], [], locals)
        in 
        mk_block pos (aux1 @ [Havoc (es1, pos)]), locals          
    | If (cond, t, e, pos) ->
        let cond1, aux, locals = flatten_expr scope [] locals cond in
        let t1, locals = flatten scope locals returns t in
        let e1, locals = flatten scope locals returns e in
        mk_block pos (aux @ [If (cond1, t1, e1, pos)]), locals
    | Loop (inv, preb, cond, postb, pos) ->
        let _ = 
          List.iter 
            (function Invariant (e, _) -> check_side_effects e)
            inv
        in
        let preb1, locals = flatten pos locals returns preb in
        let cond1, aux, locals = flatten_expr pos [] locals cond in
        let postb1, locals = flatten pos locals returns postb in
        Loop (inv, mk_block pos ([preb1] @ aux), cond1, postb1, pos), locals
    | Return ([ProcCall (id, args, cpos)], pos) ->
        let args1, aux1, locals = 
          List.fold_right 
            (fun e (es, aux, locals) ->
              let e1, aux1, locals = flatten_expr scope aux locals e in
              e1 :: es, aux1, locals
            ) 
            args ([], [], locals)
        in 
        let rts = List.map (fun id -> Ident (id, cpos)) returns in
        Block ([Assign (rts, [ProcCall (id, args1, cpos)], pos); 
                Return (rts, pos)], pos), locals
    | Return (es, pos) ->
        let es1, aux1, locals = 
          List.fold_right 
            (fun e (es, aux, locals) ->
              let e1, aux1, locals = flatten_expr scope aux locals e in
              e1 :: es, aux1, locals
            ) 
            es ([], [], locals)
        in 
        mk_block pos (aux1 @ [Return (es1, pos)]), locals
  in
  let procs =
    IdMap.fold
      (fun _ decl procs ->
        let body, locals = flatten decl.p_pos decl.p_locals decl.p_returns decl.p_body in
        let decl1 = { decl with p_locals = locals; p_body = body } in
        IdMap.add decl.p_name decl1 procs)
      cu.proc_decls IdMap.empty
  in
  { cu with proc_decls = procs }

(** Type check compilation unit [cu]. Missing type annotations are inferred along the way.*)
let infer_types cu =
  let check_spec locals pure e =
    let ty = if pure then BoolType else PermType in
    infer_types cu locals ty e
  in
  let rec check_stmt proc =
    let locals = proc.p_locals in
    function
    | Skip pos -> Skip pos
    | Block (stmts, pos) ->
        Block (List.map (check_stmt proc) stmts, pos)
    | LocalVars (_, _, pos) ->
        failwith "infer_types: LocalVars should have been eliminated"
    | Assume (e, pure, pos) ->
        Assume (check_spec locals pure e, pure, pos)
    | Assert (e, pure, pos) ->
        Assert (check_spec locals pure e, pure, pos)
    | Assign (lhs, [ProcCall (id, args, cpos) as e], pos) ->
        let decl = IdMap.find id cu.proc_decls in
        let rtys =
          List.map (fun fid ->
            let vdecl = IdMap.find fid decl.p_locals in
            vdecl.v_type)
            decl.p_returns
        in
        let lhs1 =
          try List.map2 (infer_types cu locals) rtys lhs
          with Invalid_argument _ -> 
            ProgError.error cpos 
              (Printf.sprintf "Procedure %s has %d return value(s)" 
                 (fst id) (List.length rtys))
        in
        let e1 = infer_types cu locals AnyType e in
        Assign (lhs1, [e1], pos)
    | Assign (lhs, rhs, pos) ->
        let rhs1, tys =
          Util.map_split (fun e ->
            let e1 = infer_types cu locals AnyType e in
            let ty =
              match type_of_expr cu locals e with
              | PermType ->
                  ProgError.error (pos_of_expr e) "Permissions cannot be assigned"
              | ty -> ty
            in
            e1, ty) rhs
        in
        let lhs1 =
          try
            List.map2 (infer_types cu locals) tys lhs
          with Invalid_argument _ ->
            assignment_mismatch_error pos
        in
        let rhs2 =
          List.map2
            (fun e1 e2 -> infer_types cu locals (type_of_expr cu locals e1) e2)
            lhs1 rhs1          
        in
        Assign (lhs1, rhs2, pos)
    | Dispose (e, pos) -> 
        let e1 = infer_types cu locals AnyRefType e in
        Dispose (e1, pos)
    | Havoc (es, pos) ->
        let es1 =
          List.map (fun e ->
            let e1 = infer_types cu locals AnyType e in
            match type_of_expr cu locals e1 with
            | PermType ->
                ProgError.error (pos_of_expr e) "Permissions cannot be assigned"
            | _ -> e1)
            es
        in
        Havoc (es1, pos)
    | If (cond, t, e, pos) ->
        let cond1 = infer_types cu locals BoolType cond in
        let t1 = check_stmt proc t in
        let e1 = check_stmt proc e in
        If (cond1, t1, e1, pos)
    | Loop (inv, preb, cond, postb, pos) ->
        let inv1 = 
          List.map 
            (function Invariant (e, pure) ->
              Invariant (check_spec locals pure e, pure))
            inv
        in
        let preb1 = check_stmt proc preb in
        let cond1 = infer_types cu locals BoolType cond in
        let postb1 = check_stmt proc postb in
        Loop (inv1, preb1, cond1, postb1, pos)
    | Return (es, pos) ->
        let rtys =
          List.map (fun id -> (IdMap.find id locals).v_type) proc.p_returns
        in
        let es1 =
          try List.map2 (infer_types cu locals) rtys es
          with Invalid_argument _ ->
            ProgError.error pos 
              (Printf.sprintf "Procedure %s returns %d values(s), found %d" 
                 (fst proc.p_name) (List.length rtys) (List.length es))
        in
        Return (es1, pos)
  in
  let preds =
    IdMap.fold
      (fun id pred preds ->
        let body = infer_types cu pred.pr_locals BoolType pred.pr_body in
        let _ =
          List.iter (fun vid ->
            let vdecl = IdMap.find vid pred.pr_locals in
            match vdecl.v_type with
            | SetType (StructType _)
            | SetType (ArrayType _)
            | SetType (ArrayCellType _) -> ()
            | _ -> footprint_declaration_error vid vdecl.v_pos)
            pred.pr_footprints
        in
        let pred1 = { pred with pr_body = body } in
        IdMap.add id pred1 preds)
      cu.pred_decls IdMap.empty
  in
  let procs =
    IdMap.fold
      (fun _ proc procs ->
        let contracts =
          List.map (function
            | Requires (e, pure) -> Requires (check_spec proc.p_locals pure e, pure)
            | Ensures (e, pure) -> Ensures (check_spec proc.p_locals pure e, pure)) proc.p_contracts
        in
        let body = check_stmt proc proc.p_body in
        let proc1 = { proc with p_contracts = contracts; p_body = body } in
        IdMap.add proc.p_name proc1 procs)
      cu.proc_decls IdMap.empty
  in
  let bg_theory =
    List.map
      (fun (e, pos) -> (check_spec IdMap.empty true e, pos) )
      cu.background_theory
  in
  { cu with pred_decls = preds; proc_decls = procs; background_theory = bg_theory; }


(** Converts abstract syntax into c program string.
 *  Assumes that [cu] has been type-checked and flattened.
 *)
let convert cu = 
 let include_string = 
    match cu with 
    | {includes = is; var_decls = vs; struct_decls = ds; proc_decls = pos; pred_decls = pes; background_theory = bt}-> "success"
  in 
  include_string

(** Convert compilation unit [cu] to string containing a C program. *)
let to_program_string cu =
  let cu1 = resolve_names cu in
  let cu2 = flatten_exprs cu1 in
  let cu3 = infer_types cu2 in
  convert cu3
