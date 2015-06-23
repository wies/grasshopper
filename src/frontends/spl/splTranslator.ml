(** {5 Translation of SPL programs to internal representation } *)

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
          | ArrayType _ | AnyType -> Length (idx1, pos)
          | ty -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("cells", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayType _ | AnyType -> ArrayCells (idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("array", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayCellType _ | AnyType -> ArrayOfCell (idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("index", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayCellType _ | AnyType -> IndexOfCell (idx1, pos)
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
      | ProcCall (("Btwn" as name, _ as id), args, pos)
      | ProcCall (("Reach" as name, _ as id), args, pos)
      | ProcCall (("Frame" as name, _ as id), args, pos) ->
          let args1 = List.map (re locals tbl) args in
          (match name, args1 with
          | "Btwn", [fld; x; y; z] ->
              BtwnPred (fld, x, y, z, pos)
          | "Reach", [fld; x; y] ->
              BtwnPred (fld, x, y, y, pos)
          | "Frame", [set1; set2; fld1; fld2] ->
              FramePred (set1, set2, fld1, fld2, pos)
          | _ -> pred_arg_mismatch_error pos id 4)
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
  let rec resolve_stmt first_block locals tbl = function
    | Skip pos -> Skip pos, locals, tbl
    | Block (stmts0, pos) ->
        let tbl1 = if first_block then tbl else SymbolTbl.push tbl in
        let stmts, locals, _ = 
          List.fold_left
            (fun (stmts, locals, tbl) stmt0  ->
              let stmt, locals, tbl = resolve_stmt false locals tbl stmt0 in
              stmt :: stmts, locals, tbl
            ) 
            ([], locals, tbl1) stmts0
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
        let t1, locals, _ = resolve_stmt false locals tbl t in
        let e1, locals, _ = resolve_stmt false locals tbl e in
        If (resolve_expr locals tbl cond, t1, e1, pos), locals, tbl
    | Loop (inv, preb, cond, postb, pos) ->
        let inv1 = 
          List.fold_right 
            (function Invariant (e, pure) -> fun inv1 ->
              Invariant (resolve_expr locals tbl e, pure) :: inv1
            ) 
            inv []
        in
        let preb1, locals, _ = resolve_stmt false locals tbl preb in
        let cond1 = resolve_expr locals tbl cond in
        let postb1, locals, _ = resolve_stmt false locals tbl postb in
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
        let body, locals, _ = resolve_stmt true locals0 tbl0 decl.p_body in
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
    | (BtwnPred (e1, e2, e3, e4, pos) as e)
    | (FramePred (e1, e2, e3, e4, pos) as e) ->
        check_side_effects [e1; e2; e3; e4];
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

(** Rewrite Boolean expressions to make the short-circuit evaluation semantics explicit.*)
let make_conditionals_lazy cu =
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
  let rec process_stmt scope locals = function
    | If (BinaryOp(e1, OpOr, e2, _, p1), s1, s2, p2) -> If (e1, s1, If (e2, s1, s2, p1), p2), locals
    | Loop (invs, preb, BinaryOp (e1, OpOr, e2, _, pos1), postb, pos) ->
       let aux_id, locals = decl_aux_var "loop_cond" BoolType pos scope locals
       in
       Loop (Invariant (BinaryOp (Ident (aux_id, pos),
				  OpEq,
				  BinaryOp (e1, OpOr, e2, BoolType, pos1),
				  BoolType,
				  pos),
			true) :: invs,
	     Block (
		 [preb;
		  If (e1,
		      Assign ([Ident (aux_id, pos)], [BoolVal (true, pos)], pos),
		      If (e2,
			  Assign ([Ident (aux_id, pos)], [BoolVal (true, pos)], pos),
			  Assign ([Ident (aux_id, pos)], [BoolVal (false, pos)], pos),
			  pos),
		      pos)],
		 pos),
	     Ident (aux_id, pos1),
	     postb,
	     pos), locals
    | Block (ss, p) ->
       let ss, locals = List.fold_right
			  (fun s (s_list, locals) ->
			   let new_s, locals = process_stmt scope locals s
			   in
			   ([new_s] @ s_list), locals)
			  ss ([], locals)
       in
       Block (ss, p), locals
    | stmt -> stmt, locals
  in
  let procs =
    IdMap.fold
      (fun _ decl procs ->
        let body, locals = process_stmt decl.p_pos decl.p_locals decl.p_body in
        let decl1 = { decl with p_body = body; p_locals = locals } in
        IdMap.add decl.p_name decl1 procs)
      cu.proc_decls IdMap.empty
  in
  { cu with proc_decls = procs }


(** Convert compilation unit [cu] to abstract syntax of the intermediate language.
 *  Assumes that [cu] has been type-checked and flattened.
 *)
let convert cu =
  let find_var_decl pos locals id =
    try IdMap.find id locals 
    with Not_found -> 
      try IdMap.find id cu.var_decls
      with Not_found ->
        ProgError.error pos ("Unable to find identifier " ^ string_of_ident id)
  in
  let field_type pos fld_id locals =
    let fdecl = find_var_decl pos locals fld_id in
    fdecl.v_type
    (*with Not_found ->
      ProgError.error pos 
        ("Struct " ^ fst id ^ " does not have a field named " ^ fst fld_id)*)
  in
  let convert_type ty pos =
    let rec ct = function
      | StructType id -> Loc (FreeSrt id)
      | AnyRefType -> Loc (FreeSrt ("Null", 0))
      | MapType (dtyp, rtyp) -> Map (ct dtyp, ct rtyp)
      | SetType typ -> Set (ct typ)
      | ArrayType typ -> Loc (Array (ct typ))
      | ArrayCellType typ -> Loc (ArrayCell (ct typ))
      | IntType -> Int
      | BoolType -> Bool
      | ty -> failwith ("cannot convert type " ^ string_of_type ty ^ " near position " ^ string_of_src_pos pos)
    in
    ct ty
  in
  let convert_var_decl decl = 
    { var_name = decl.v_name;
      var_orig_name = fst decl.v_name;
      var_sort = convert_type decl.v_type decl.v_pos;
      var_is_ghost = decl.v_ghost;
      var_is_implicit = decl.v_implicit;
      var_is_aux = decl.v_aux;
      var_pos = decl.v_pos;
        var_scope = decl.v_scope;
    }
  in
  let rec convert_term locals = function
    | Null (ty, pos) ->
        let cty = convert_type ty pos in
        let ssrt = GrassUtil.struct_sort_of_sort cty in
        GrassUtil.mk_null ssrt
    | Setenum (ty, es, pos) ->
        let ts = List.map (convert_term locals) es in
        let elem_ty =  convert_type ty pos in
        (match es with
        | [] -> GrassUtil.mk_empty (Set elem_ty)
        | _ -> GrassUtil.mk_setenum ts)
    | IntVal (i, _) ->
        GrassUtil.mk_int i
    | BoolVal (b, pos) ->
        App (BoolConst b, [], Bool)
    | Read (map, idx, pos) -> 
        let tmap = convert_term locals map in
        let tidx = convert_term locals idx in
        GrassUtil.mk_read tmap tidx
    | Length (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_length t
    | ArrayOfCell (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_array_of_cell t
    | IndexOfCell (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_index_of_cell t
    | ArrayCells (e, pos) ->
        let t = convert_term locals e in
        GrassUtil.mk_array_cells t
    | PredApp (id, es, pos) ->
        let decl = IdMap.find id cu.pred_decls in
        let ts = List.map (convert_term locals) es in 
        (match decl.pr_outputs with
        | [res] ->
            let res_decl = IdMap.find res decl.pr_locals in
            let res_srt = convert_type res_decl.v_type pos in
            GrassUtil.mk_free_fun res_srt id ts
        | [] ->
            GrassUtil.mk_free_fun Bool id ts
        | _ -> failwith "unexpected expression")
    | BinaryOp (e1, (OpDiff as op), e2, ty, _)
    | BinaryOp (e1, (OpUn as op), e2, ty, _)      
    | BinaryOp (e1, (OpInt as op), e2, ty, _) ->
        let mk_app =
          match op with
          | OpDiff -> GrassUtil.mk_diff
          | OpUn -> (fun t1 t2 -> GrassUtil.mk_union [t1; t2])
          | OpInt -> (fun t1 t2 -> GrassUtil.mk_inter [t1; t2])
          | _ -> failwith "unexpected operator"
        in
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        mk_app t1 t2
    | BinaryOp (e1, (OpMinus as op), e2, ty, _)
    | BinaryOp (e1, (OpPlus as op), e2, ty, _)
    | BinaryOp (e1, (OpMult as op), e2, ty, _)
    | BinaryOp (e1, (OpDiv as op), e2, ty, _) ->
        let mk_app =
          match op with
          | OpMinus -> GrassUtil.mk_minus
          | OpPlus -> GrassUtil.mk_plus
          | OpMult -> GrassUtil.mk_mult
          | OpDiv -> GrassUtil.mk_div
          | _ -> failwith "unexpected operator"
        in
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        mk_app t1 t2
    | UnaryOp (OpPlus, e, _) ->
        convert_term locals e
    | UnaryOp (OpMinus, e, _) ->
        let t = convert_term locals e in
        GrassUtil.mk_uminus t
    | Ident (id, pos) ->
        let decl = find_var_decl pos locals id in
        let srt = convert_type decl.v_type pos in
        GrassUtil.mk_free_const srt decl.v_name
    | BinaryOp (e1, OpIn, e2, ty, pos) ->
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        GrassUtil.mk_elem_term t1 t2
    | e -> failwith ("unexpected expression at " ^ string_of_src_pos (pos_of_expr e))
  in
  let rec convert_grass_form locals = function
    | BoolVal (b, pos) -> GrassUtil.mk_srcpos pos (GrassUtil.mk_bool b)
    | BtwnPred (fld, x, y, z, pos) ->
        let tfld = convert_term locals fld in
        let tx = convert_term locals x in
        let ty = convert_term locals y in
        let tz = convert_term locals z in
        GrassUtil.mk_srcpos pos (GrassUtil.mk_btwn tfld tx ty tz)
    | FramePred (set1, set2, fld1, fld2, pos) ->
        let tset1 = convert_term locals set1 in
        let tset2 = convert_term locals set2 in
        let tfld1 = convert_term locals fld1 in
        let tfld2 = convert_term locals fld2 in
        GrassUtil.mk_srcpos pos (GrassUtil.mk_btwn tset1 tset2 tfld1 tfld2)
    | Quant (q, decls, f, pos) ->
        let mk_guard = match q with
          | Forall -> GrassUtil.mk_implies
          | Exists -> fun f g -> GrassUtil.mk_and [f; g] 
        in
        let mk_quant vs f =
          let f0, ann = match f with
            | Binder (_, [], f0, ann) -> f0, ann
            | f0 -> f0, []
          in
          let f1 = match q with
            | Forall -> GrassUtil.mk_forall vs f0
            | Exists -> GrassUtil.mk_exists vs f0
          in
          GrassUtil.annotate f1 ann
        in
        let (vars, (domains, locals1)) =
          Util.fold_left_map
            (fun (accD,accL) decl -> match decl with
              | GuardedVar (id, e) ->
                let e1 = convert_term locals e in
                (match type_of_expr cu locals e with
                | SetType elem_srt ->
                  let decl = var_decl id elem_srt false false pos pos in
                  let elem_srt = convert_type elem_srt pos in
                  let v_id = GrassUtil.mk_var elem_srt id in
                  (id, elem_srt), ((GrassUtil.mk_elem v_id e1) :: accD, IdMap.add id decl accL)
                | _ -> failwith "unexpected type")
              | UnguardedVar decl ->
                let id = decl.v_name in
                let ty = decl.v_type in
                (id, convert_type ty pos), (accD, IdMap.add id decl accL)
            )
            ([],locals)
            decls
        in
        let subst = 
          List.fold_right (fun (id, srt) subst -> 
            IdMap.add id (GrassUtil.mk_var srt id) subst)
            vars IdMap.empty
        in
        let f1 = convert_grass_form locals1 f in
        let f2 = mk_guard (GrassUtil.mk_and domains) f1 in
        let f3 = GrassUtil.subst_consts subst f2 in
        GrassUtil.mk_srcpos pos (mk_quant vars f3)
    | BinaryOp (e1, OpEq, e2, _, pos) ->
        (match type_of_expr cu locals e1 with
        | BoolType ->
            let f1 = convert_grass_form locals e1 in
            let f2 = convert_grass_form locals e2 in
            GrassUtil.mk_srcpos pos (GrassUtil.mk_iff f1 f2)
        | _ ->
            let t1 = convert_term locals e1 in
            let t2 = convert_term locals e2 in
            GrassUtil.mk_srcpos pos (GrassUtil.mk_eq t1 t2))
    | BinaryOp (e1, (OpGt as op), e2, ty, pos)
    | BinaryOp (e1, (OpLt as op), e2, ty, pos)
    | BinaryOp (e1, (OpGeq as op), e2, ty, pos)
    | BinaryOp (e1, (OpLeq as op), e2, ty, pos) ->
        let mk_int_form =
          match op with
          | OpGt -> GrassUtil.mk_gt
          | OpLt -> GrassUtil.mk_lt
          | OpGeq -> GrassUtil.mk_geq
          | OpLeq -> GrassUtil.mk_leq
          | _ -> failwith "unexpected operator"
        in
        let mk_set_form =
          match op with
          | OpGt -> (fun s t -> GrassUtil.mk_strict_subset t s)
          | OpLt -> GrassUtil.mk_strict_subset
          | OpGeq -> (fun s t -> GrassUtil.mk_subseteq t s)
          | OpLeq -> GrassUtil.mk_subseteq
          | _ -> failwith "unexpected operator"
        in
        let t1 = convert_term locals e1 in
        let t2 = convert_term locals e2 in
        (match type_of_expr cu locals e1 with
        | IntType -> GrassUtil.mk_srcpos pos (mk_int_form t1 t2)
        | SetType _ -> GrassUtil.mk_srcpos pos (mk_set_form t1 t2)
        | ty -> failwith ("unexpected type " ^ string_of_type ty ^ " at " ^ string_of_src_pos pos)) 
    | UnaryOp (OpNot, e, pos) ->
        let f = convert_grass_form locals e in
        GrassUtil.mk_not f
    | BinaryOp (e1, (OpAnd as op), e2, _, _)
    | BinaryOp (e1, (OpOr as op), e2, _, _)
    | BinaryOp (e1, (OpImpl as op), e2, _, _) ->
        let f1 = convert_grass_form locals e1 in
        let f2 = convert_grass_form locals e2 in
        let mk_form = 
          match op with
          | OpAnd -> fun f1 f2 -> GrassUtil.smk_and [f1; f2]
          | OpOr -> fun f1 f2 -> GrassUtil.smk_or [f1; f2]
          | OpImpl -> GrassUtil.mk_implies           
          | _ -> failwith "unexpected operator"
        in
        mk_form f1 f2
    | Annot (e, CommentAnnot c, pos) ->
        let f = convert_grass_form locals e in
        GrassUtil.annotate f [Name (c, 0)]
    | Annot (e, GeneratorAnnot (es, ge), pos) ->
        let f = convert_grass_form locals e in
        let es1 = List.map (convert_term locals) es in
        let ge1 = convert_term locals ge in
        let gts = GrassUtil.ground_terms (Atom (ge1, [])) in
        (*let filter id sm =
           
        in*)
        let matches = 
          List.map (fun e -> 
            let ce = GrassUtil.free_consts_term e in
            let ce_occur_below ts =
              List.exists 
                (function App (FreeSym id, [], _) -> IdSet.mem id ce | _ -> false)
                ts
               in
            (*let rec ce_occur_below = function
              | App (FreeSym id, [], _) -> IdSet.mem id ce
              | App (_, ts, _) as t ->
                  t <> e && List.exists ce_occur_below ts
              | _ -> false
            in*)
            let flt = 
              TermSet.fold 
                (fun t acc -> match t with
                  | App (FreeSym sym, (_ :: _ as ts), _) when ce_occur_below ts ->
                    (FilterSymbolNotOccurs (FreeSym sym)) :: acc
                  | App (Read, (App (FreeSym sym, [], srt) :: _ as ts), _) when ce_occur_below ts ->
                    (FilterReadNotOccurs (GrassUtil.name sym, ([], srt))) :: acc
                  | _ -> acc)
                gts [FilterNotNull]
            in
            Match (e, flt)) es1
        in
        GrassUtil.annotate f [TermGenerator (matches, [ge1])]
    | e ->
        let t = convert_term locals e in
        Grass.Atom (t, [SrcPos (pos_of_expr e)])
  in
  let rec convert_sl_form locals = function
    | Emp pos -> SlUtil.mk_emp (Some pos)
    | Access (e, pos) ->
        let t = convert_term locals e in
        SlUtil.mk_region ~pos:pos t
    | PredApp (id, es, pos) ->
        let ts = List.map (convert_term locals) es in 
        SlUtil.mk_pred ~pos:pos id ts
    | BinaryOp (e1, OpPts, e2, _, pos) ->
        let fld, ind = 
          match convert_term locals e1 with
          | App (Read, [fld; ind], _) -> fld, ind
          | _ -> 
              ProgError.error (pos_of_expr e1) 
                "Expected field access on left-hand-side of points-to predicate"
        in
        let t2 = convert_term locals e2 in
        SlUtil.mk_pts ~pos:pos fld ind t2
    | BinaryOp (e1, (OpSepStar as op), e2, _, pos)
    | BinaryOp (e1, (OpSepPlus as op), e2, _, pos)
    | BinaryOp (e1, (OpSepIncl as op), e2, _, pos) ->
        let mk_op = function
          | OpSepStar -> SlUtil.mk_sep_star
          | OpSepPlus -> SlUtil.mk_sep_plus
          | OpSepIncl -> SlUtil.mk_sep_incl
          | _ -> failwith "unexpected operator"
        in
        let f1 = convert_sl_form locals e1 in
        let f2 = convert_sl_form locals e2 in
        mk_op ~pos:pos op f1 f2
    | BinaryOp (e1, (OpAnd as op), e2, PermType, _)
    | BinaryOp (e1, (OpOr as op), e2, PermType, _) ->
        let f1 = convert_sl_form locals e1 in
        let f2 = convert_sl_form locals e2 in
        let mk_form = 
          match op with
          | OpAnd -> SlUtil.mk_and
          | OpOr -> SlUtil.mk_or
          | _ -> failwith "unexpected operator" 
        in
        mk_form f1 f2
    | Quant (q, decls, f, pos) when q = Exists ->
        let vars, locals1 = 
          List.fold_right (fun decl (vars, locals1) -> match decl with
            | UnguardedVar decl ->
              let id = decl.v_name in
              let ty = decl.v_type in
              (id, convert_type ty pos) :: vars, 
              IdMap.add id decl locals1
            | GuardedVar _ -> failwith "unexpected Guarded variable"
            )
            decls ([], locals)
        in
        let subst = 
          List.fold_right (fun (id, srt) subst -> 
            IdMap.add id (GrassUtil.mk_var srt id) subst)
            vars IdMap.empty
        in
        let mk_quant = match q with
        | Forall -> SlUtil.mk_forall 
        | Exists -> SlUtil.mk_exists
        in
        let f1 = convert_sl_form locals1 f in
        let f2 = SlUtil.subst_consts subst f1 in
        mk_quant ~pos:pos vars f2
    | e ->
        let f = convert_grass_form locals e in
        Pure (f, Some (pos_of_expr e))
  in
  let convert_spec_form pure locals e name msg =
    let f = 
      if pure 
      then FOL (convert_grass_form locals e)
      else SL (convert_sl_form locals e)
    in
    mk_spec_form f name msg (pos_of_expr e)
  in
  let convert_loop_contract proc_name locals contract =
    List.map
      (function Invariant (e, pure) -> 
        let msg caller =
          if caller = proc_name then
            (Printf.sprintf 
               "An invariant might not hold before entering a loop in procedure %s"
               (string_of_ident proc_name),
             ProgError.mk_error_info "This is the loop invariant that might not hold initially")
          else 
            (Printf.sprintf 
               "An invariant might not be maintained by a loop in procedure %s"
               (string_of_ident proc_name),
             ProgError.mk_error_info "This is the loop invariant that might not be maintained")
        in
        (*let pos = pos_of_expr e in*)
        convert_spec_form pure locals e "invariant" (Some msg)
      )
      contract
  in
  let rec convert_stmt proc = 
    let convert_lhs es = 
      let ts = List.map (convert_term proc.p_locals) es in
      match ts with
      | [App (Read, [App (FreeSym fld, [], _); ind], _)] ->
          [fld], Some ind
      | _ -> 
          let ids = 
            List.map 
              (function 
                | Ident (id, _) -> id
                | e -> 
                    ProgError.error (pos_of_expr e) 
                      "Only variables are allowed on left-hand-side of simultaneous assignments"
              ) es                
          in
          ids, None
    in
    function
      | Skip pos -> mk_seq_cmd [] pos
      | Block (stmts, pos) ->
          let cmds = List.map (convert_stmt proc) stmts in
          mk_seq_cmd cmds pos
      | Assume (e, pure, pos) ->
          let sf = convert_spec_form pure proc.p_locals e "assume" None in
          mk_assume_cmd sf pos
      | Assert (e, pure, pos) ->
          let sf = convert_spec_form pure proc.p_locals e "assert" None in
          mk_assert_cmd sf pos
      | Assign (lhs, [ProcCall (id, es, cpos)], pos) ->
          let args = 
            List.map (convert_term proc.p_locals) es
          in 
          let lhs_ids, _ = convert_lhs lhs in
          mk_call_cmd lhs_ids id args cpos
      | Assign ([lhs], [New ((StructType _ as ty), es, npos)], pos)
      | Assign ([lhs], [New ((ArrayType _ as ty), es, npos)], pos) ->
          let lhs_ids, _ = convert_lhs [lhs] in
          let ts = List.map (convert_term proc.p_locals) es in
          let lhs_id = List.hd lhs_ids in
          mk_new_cmd lhs_id (convert_type ty npos) ts pos
      | Assign (lhs, rhs, pos) ->
          let rhs_ts = List.map (convert_term proc.p_locals) rhs in
          let lhs_ids, ind_opt = convert_lhs lhs in
          let cmd =
            (match ind_opt with
            | Some t ->
                let fld_id = List.hd lhs_ids in
                let fld_srt = convert_type (field_type pos fld_id proc.p_locals) pos in
                let fld = GrassUtil.mk_free_const fld_srt fld_id in
                mk_assign_cmd lhs_ids [GrassUtil.mk_write fld t (List.hd rhs_ts)] pos
            | None -> mk_assign_cmd lhs_ids rhs_ts pos)
          in
          cmd
      | Dispose (e, pos) ->
          let t = convert_term proc.p_locals e in
          mk_dispose_cmd t pos
      | Havoc (es, pos) ->
          let ids = 
            List.map
              (function 
                | Ident (id, _) -> id
                | e -> ProgError.error (pos_of_expr e) "Only variables can be havoced"
              )
              es
          in 
          mk_havoc_cmd ids pos
      | If (c, t, e, pos) ->
          let cond = convert_grass_form proc.p_locals c in
          let t_cmd = convert_stmt proc t in
          let e_cmd = convert_stmt proc e in
          let t_msg = "The 'then' branch of this conditional has been taken on the error trace" in
          let e_msg = "The 'else' branch of this conditional has been taken on the error trace" in
          mk_ite cond (pos_of_expr c) t_cmd e_cmd t_msg e_msg pos
      | Loop (contract, preb, cond, postb, pos) ->
          let preb_cmd = convert_stmt proc preb in
          let cond_pos = pos_of_expr cond in
          let cond = convert_grass_form proc.p_locals cond in
          let invs = convert_loop_contract proc.p_name proc.p_locals contract in
          let postb_cmd = convert_stmt proc postb in
          mk_loop_cmd invs preb_cmd cond cond_pos postb_cmd pos
      | Return (es, pos) ->
          let ts = List.map (convert_term proc.p_locals) es in
          mk_return_cmd ts pos
      | _ -> failwith "unexpected statement"
  in
  let prog =
    IdMap.fold
      (fun id decl prog -> declare_global prog (convert_var_decl decl))
      cu.var_decls empty_prog
  in
  let prog =
    IdMap.fold 
      (fun id decl prog ->
        let body = convert_grass_form decl.pr_locals decl.pr_body in
        let locals = IdMap.map convert_var_decl decl.pr_locals in
        let fun_terms f =
          let rec ft acc = function
            | App (sym, _ :: _, srt) as t when GrassUtil.is_free_symbol sym || srt <> Bool ->
                if IdSet.is_empty (GrassUtil.fv_term t)
                then TermSet.add t acc else acc
            | App (_, ts, _) ->
                List.fold_left ft acc ts
            | _ -> acc
          in
          GrassUtil.fold_terms ft TermSet.empty f
        in
        let sorted_vs =
          List.map
            (fun x ->
              let var = IdMap.find x locals in
              x, var.var_sort)
            (decl.pr_formals @ decl.pr_footprints)
        in
        let vs = List.map (fun (x, srt) -> GrassUtil.mk_free_const srt x) sorted_vs in
        let m, kgen = match decl.pr_outputs with
        | [] ->
            let mt = GrassUtil.mk_free_fun Bool id vs in
            let m = Match (mt, []) in
            m, [TermGenerator ([m], [GrassUtil.mk_known mt])]
        | [x] ->
            let var = IdMap.find x locals in
            Match (GrassUtil.mk_free_fun var.var_sort id vs, []), []
        | _ -> failwith "Functions may only have a single return value."
        in
        let rec add_match = function
          | Binder (b, vs, f, annots) ->
              let annots1 =
                List.map (function TermGenerator (ms, ts) -> TermGenerator (m :: ms, ts) | a -> a) annots
              in
              Binder (b, vs, add_match f, annots1)
          | BoolOp (op, fs) ->
              BoolOp (op, List.map add_match fs)
          | f -> f
        in
        let rec add_generators f =
          match f with
          | BoolOp (And, fs) ->
              BoolOp (And, List.map add_generators fs)
          | _ ->
              let ft = fun_terms f in
              let generators =
                (if TermSet.is_empty ft then []
                else [TermGenerator ([m], TermSet.elements ft)])
                @ kgen              
              in
              GrassUtil.annotate f generators
        in
        let body = add_generators (add_match body) in
        let pred_decl = 
          { pred_name = id;
            pred_formals = decl.pr_formals;
            pred_outputs = decl.pr_outputs;
            pred_footprints = decl.pr_footprints;
            pred_locals = locals;
            pred_body = mk_spec_form (FOL body) (string_of_ident id) None (pos_of_expr decl.pr_body);
            pred_pos = decl.pr_pos;
            pred_accesses = IdSet.empty;
            pred_is_free = false
          }
        in
        declare_pred prog pred_decl
      )
      cu.pred_decls prog
  in
  let convert_contract proc_name locals contract =
    List.fold_right 
      (function 
        | Requires (e, pure) -> fun (pre, post) -> 
            let mk_msg caller =
              Printf.sprintf 
                "A precondition for this call of %s might not hold"
                (string_of_ident proc_name),
              ProgError.mk_error_info "This is the precondition that might not hold"
            in
            let name = "precondition of " ^ string_of_ident proc_name in
            convert_spec_form pure locals e name (Some mk_msg) :: pre, post
        | Ensures (e, pure) -> fun (pre, post) ->
            let mk_msg caller =
              Printf.sprintf 
                "A postcondition of procedure %s might not hold at this return point"
                (string_of_ident proc_name),
              ProgError.mk_error_info "This is the postcondition that might not hold"
            in 
            let name = "postcondition of " ^ string_of_ident proc_name in
            pre, convert_spec_form pure locals e name (Some mk_msg) :: post)
      contract ([], [])
  in
  let convert_body decl =
    match decl.p_body with
    | Skip _ -> None
    | _ -> Some (convert_stmt decl decl.p_body)
  in
  let prog =
    IdMap.fold
      (fun id decl prog ->
        let pre, post = convert_contract decl.p_name decl.p_locals decl.p_contracts in
        let proc_decl =
          { proc_name = id;
            proc_formals = decl.p_formals;
            proc_returns = decl.p_returns;
            proc_locals = IdMap.map convert_var_decl decl.p_locals;
            proc_precond = pre;
            proc_postcond = post;
            proc_body = convert_body decl;
            proc_pos = decl.p_pos;
            proc_deps = [];
            proc_is_tailrec = false;
          } 
        in
        declare_proc prog proc_decl
      )
      cu.proc_decls prog
  in
  let prog = 
    let specs =
      List.map
        ( fun (e, pos) ->
          convert_spec_form true IdMap.empty e "axiom" None
        )
        cu.background_theory
    in
      { prog with prog_axioms = specs @ prog.prog_axioms }
  in
  prog

(** Convert compilation unit [cu] to abstract syntax of the intermediate language. *)
let to_program cu =
  let cu1 = resolve_names cu in
  let cu2 = flatten_exprs cu1 in
  let cu3 = infer_types cu2 in
  let cu4 = make_conditionals_lazy cu3 in
  convert cu4
