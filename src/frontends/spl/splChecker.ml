(** {5 Static Checker for SPL programs } *)

open Util 
open Prog
open Sl
open Grass
open SplSyntax
open SplErrors
open SplTypeChecker

  
(** Resolve names of identifiers in compilation unit [cu] so that all identifiers have unique names.*)
let resolve_names cu = 
  let lookup_id init_id tbl pos =
    let name = GrassUtil.name init_id in
    match SymbolTbl.find tbl name with
    | Some (id, _) -> id
    | None -> unknown_ident_error init_id pos
  in 
  let check_type id types pos =
    if not (IdMap.mem id types) then
      not_a_type_error id pos
  in
  (*let check_struct id types pos =
    check_type id types pos;
    let decl = IdMap.find id types in
    match decl.t_def with
    | StructTypeDef _ -> ()
    | _ -> not_a_struct_error id pos
  in*)
  let check_proc id procs pos =
    if not (IdMap.mem id procs) then
      not_a_proc_error id pos
  in
  let check_pred id preds pos =
    if not (IdMap.mem id preds) then
      not_a_pred_error id pos
  in
  (* resolve names in type expressions *)
  let resolve_typ types pos tbl =
    let rec r = function
    | IdentType init_id ->
        let id = lookup_id init_id tbl pos in
        check_type id types pos;
        let decl = IdMap.find id types in
        (match decl.t_def with
        | StructTypeDef _ -> StructType id
        | FreeTypeDef -> IdentType id)
    | ArrayType ty -> ArrayType (r ty)
    | ArrayCellType ty -> ArrayCellType (r ty)
    | MapType (ty1, ty2) -> MapType (r ty1, r ty2)
    | SetType ty -> SetType (r ty)
    | ty -> ty
    in
    r
  in
  let declare_name pos init_id scope tbl =
    let name = GrassUtil.name init_id in
    match SymbolTbl.find_local tbl name with
    | Some _ -> redeclaration_error init_id pos
    | None ->
        let id = GrassUtil.fresh_ident name in
        (id, SymbolTbl.add tbl name (id, scope))
  in
  let declare_var types decl tbl =
    let id, tbl = declare_name decl.v_pos decl.v_name decl.v_scope tbl in
        let ty = resolve_typ types decl.v_pos tbl decl.v_type in
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
  (* resolve type names *)
  let types0, tbl =
    IdMap.fold 
      (fun init_id decl (structs, tbl) ->
        let id, tbl = declare_name decl.t_pos init_id GrassUtil.global_scope tbl in
        IdMap.add id { decl with t_name = id } structs, tbl)
      cu.type_decls (IdMap.empty, tbl)
  in
  (* resolve global variables *)
  let globals0, tbl = declare_vars cu.var_decls types0 tbl in
  (* declare struct fields *)
  let types, globals, tbl =
    IdMap.fold
      (fun id decl (types, globals, tbl) ->
        match decl.t_def with
        | StructTypeDef fields0 ->
            let fields, globals, tbl =
              IdMap.fold 
                (fun init_id fdecl (fields, globals, tbl) ->
                  let id, tbl = declare_name fdecl.v_pos init_id GrassUtil.global_scope tbl in
                  let res_type = resolve_typ types0 fdecl.v_pos tbl fdecl.v_type in
                  let typ = MapType (StructType decl.t_name, res_type) in
                  let fdecl = { fdecl with v_name = id; v_type = res_type } in
                  let gfdecl = { fdecl with v_type = typ } in
                  IdMap.add id fdecl fields, IdMap.add id gfdecl globals, tbl
                )
                fields0 (IdMap.empty, globals, tbl)
            in
            IdMap.add id { decl with t_def = StructTypeDef fields } types, 
            globals, 
            tbl
        | _ -> IdMap.add id decl types, globals, tbl
      )
      types0 (IdMap.empty, globals0, tbl)
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
      type_decls = types; 
      proc_decls = procs0;
      pred_decls = preds0;
    }
  in
  let resolve_expr locals tbl e =
    let rec re locals tbl = function
      | Setenum (ty, args, pos) ->
          let ty1 = resolve_typ types pos tbl ty in
          let args1 = List.map (re locals tbl) args in
          Setenum (ty1, args1, pos)
      | New (ty, args, pos) ->
          let ty1 = resolve_typ types pos tbl ty in 
          let args1 =  List.map (re locals tbl) args in
          New (ty1, args1, pos)
      | Read ((Ident (("length", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayType _ | AnyType -> UnaryOp (OpLength, idx1, pos)
          | ty -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("cells", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayType _ | AnyType -> UnaryOp (OpArrayCells, idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("array", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayCellType _ | AnyType -> UnaryOp (OpArrayOfCell, idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read ((Ident (("index", _), _) as map), idx, pos) ->
          let idx1 = re locals tbl idx in
          (match type_of_expr cu locals idx1 with
          | ArrayCellType _ | AnyType -> UnaryOp (OpIndexOfCell, idx1, pos)
          | _ -> Read (re locals tbl map, idx1, pos))
      | Read (map, idx, pos) ->
          Read (re locals tbl map, re locals tbl idx, pos)
      | Binder (q, decls, f, pos) ->
          let (decls1, (locals1, tbl1)) = 
            Util.fold_left_map
              (fun (locals, tbl) decl -> match decl with
              | GuardedVar (init_id, e) ->
                let e1 = re locals tbl e in
                let id, tbl1 = declare_name pos init_id pos tbl in
                (GuardedVar (id, e1)), (locals, tbl1) 
              | UnguardedVar decl ->
                let decl, tbl1 = declare_var types decl tbl in
                (UnguardedVar decl), (IdMap.add decl.v_name decl locals, tbl1)
              )
              (locals, SymbolTbl.push tbl)
              decls
          in
          let f1 = re locals1 tbl1 f in
          Binder (q, decls1, f1, pos)
      | ProcCall (("acc", _ as id), args, pos) ->
          let args1 = List.map (re locals tbl) args in
          (match args1 with
          | [arg] ->
              (match type_of_expr cu locals arg with
              | SetType _ -> 
                  PredApp (AccessPred, [re locals tbl arg], pos)
              | ty ->
                  PredApp (AccessPred, [Setenum (resolve_typ types pos tbl ty, [re locals tbl arg], pos)], pos))
          | [map; idx] ->
              (match type_of_expr cu locals map with
              | ArrayType typ ->
                  let map1 = re locals tbl map in
                  let idx1 = re locals tbl idx in
                  let cell = Read (UnaryOp (OpArrayCells, map1, pos_of_expr map1), idx1, pos) in
                  PredApp (AccessPred, [Setenum (ArrayCellType typ, [cell], pos)], pos)
              | _ -> pred_arg_mismatch_error pos id 1)
          | _ -> pred_arg_mismatch_error pos id 1)
      | ProcCall (init_id, args, pos) ->
          let args1 = List.map (re locals tbl) args in
          (match GrassUtil.name init_id with
          | "old" ->
              UnaryOp (OpOld, List.hd args1, pos)
          | "known" ->
              UnaryOp (OpKnown, List.hd args1, pos)
          | "Btwn" ->
              PredApp (BtwnPred, args1, pos)
          | "Reach" ->
              PredApp (ReachPred, args1, pos)
          | "Frame" ->
              PredApp (FramePred, args1, pos)
          | "Disjoint" ->
              PredApp (DisjointPred, args1, pos)
          | _ ->
              let id = lookup_id init_id tbl pos in
              try 
                check_proc id procs0 pos;
                ProcCall (id, args1, pos)
              with ProgError.Prog_error _ ->
                check_pred id preds0 pos;
                PredApp (Pred id, args1, pos))
      | PredApp (sym, args, pos) ->
          PredApp (sym, List.map (re locals tbl) args, pos)              
      | UnaryOp (op, e, pos) ->
          UnaryOp (op, re locals tbl e, pos)
      | BinaryOp (e1, op, e2, ty, pos) ->
          BinaryOp (re locals tbl e1, op, re locals tbl e2, ty, pos)
      | Ident (init_id, pos) ->
          let id = lookup_id init_id tbl pos in
          Ident (id, pos)
      | Annot (e, PatternAnnot p, pos) ->
          Annot (re locals tbl e, PatternAnnot (re locals tbl p), pos)
      | Annot (e, GeneratorAnnot (es, ge), pos) ->
          let es1 =
            List.map (fun (e, ids) ->
              let ids1 =
                List.map (fun init_id -> lookup_id init_id tbl pos) ids
              in
              re locals tbl e, ids1)
              es
          in
          Annot (re locals tbl e, GeneratorAnnot (es1, re locals tbl ge), pos)
      | Annot (e, ann, pos) ->
          Annot (re locals tbl e, ann, pos)
      | e -> e
    in
    re locals tbl e
  in
  let rec resolve_stmt first_block in_loop locals tbl = function
    | Skip pos -> Skip pos, locals, tbl
    | Block (stmts0, pos) ->
        let tbl1 = if first_block then tbl else SymbolTbl.push tbl in
        let stmts, locals, _ = 
          List.fold_left
            (fun (stmts, locals, tbl) stmt0  ->
              let stmt, locals, tbl = resolve_stmt false in_loop locals tbl stmt0 in
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
                let decl, tbl = declare_var types decl tbl in
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
        let t1, locals, _ = resolve_stmt false in_loop locals tbl t in
        let e1, locals, _ = resolve_stmt false in_loop locals tbl e in
        If (resolve_expr locals tbl cond, t1, e1, pos), locals, tbl
    | Loop (inv, preb, cond, postb, pos) ->
        let inv1 = 
          List.fold_right 
            (function Invariant (e, pure) -> fun inv1 ->
              Invariant (resolve_expr locals tbl e, pure) :: inv1
            ) 
            inv []
        in
        let preb1, locals, _ = resolve_stmt false true locals tbl preb in
        let cond1 = resolve_expr locals tbl cond in
        let postb1, locals, _ = resolve_stmt false true locals tbl postb in
        Loop (inv1, preb1, cond1, postb1, pos), locals, tbl
    | Return (es, pos) ->
        if in_loop then return_in_loop_error pos;
        Return (List.map (resolve_expr locals tbl) es, pos), locals, tbl
  in
  (* declare and resolve local variables *)
  let resolve_contracts contracts returns locals tbl =
    let pre_locals, pre_tbl =
      List.fold_left
        (fun (pre_locals, pre_tbl) id ->
          IdMap.remove id pre_locals,
          SymbolTbl.remove pre_tbl (GrassUtil.name id))
        (locals, tbl)
        returns
    in
    List.map 
      (function 
        | Requires (e, pure) -> Requires (resolve_expr pre_locals pre_tbl e, pure)
        | Ensures (e, pure) -> Ensures (resolve_expr locals tbl e, pure)
      )
      contracts
  in
  let procs =
    IdMap.fold
      (fun _ decl procs ->
        let locals0, tbl0 = declare_vars decl.p_locals types (SymbolTbl.push tbl) in
        let formals = List.map (fun id -> lookup_id id tbl0 decl.p_pos) decl.p_formals in
        let returns = List.map (fun id -> lookup_id id tbl0 decl.p_pos) decl.p_returns in
        let contracts = resolve_contracts decl.p_contracts returns locals0 tbl0 in
        let body, locals, _ = resolve_stmt true false locals0 tbl0 decl.p_body in
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
        let locals, tbl = declare_vars decl.pr_locals types (SymbolTbl.push tbl) in
        let body = Opt.map (resolve_expr locals tbl) decl.pr_body in
        let formals = List.map (fun id -> lookup_id id tbl decl.pr_pos) decl.pr_formals in
        let outputs = List.map (fun id -> lookup_id id tbl decl.pr_pos) decl.pr_outputs in
        let contracts = resolve_contracts decl.pr_contracts outputs locals tbl in
        let decl1 = 
          { decl with 
            pr_formals = formals;
            pr_outputs = outputs; 
            pr_locals = locals;
            pr_contracts = contracts;
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
    type_decls = types; 
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
  let rec flatten_expr_list scope aux locals es =
     List.fold_right (fun e (es1, aux1, locals) ->
       let e1, aux1, locals = flatten_expr scope aux1 locals e in
       e1 :: es1, aux1, locals)
      es ([], aux, locals)
  and flatten_expr scope aux locals = function
    | Setenum (ty, args, pos) ->
        let args1, aux1, locals = flatten_expr_list scope aux locals args in
        Setenum (ty, args1, pos), aux1, locals
    | New (ty, args, pos) ->
        let aux_id, locals = decl_aux_var "tmp" ty pos scope locals in
        let args1, aux1, locals = flatten_expr_list scope aux locals args in
        let aux_var = Ident (aux_id, pos) in
        let alloc = Assign ([aux_var], [New (ty, args1, pos)], pos) in
        let aux_cmds, aux_funs = aux1 in
        aux_var, (alloc :: aux_cmds, aux_funs), locals
    | Read (map, idx, pos) ->
        let map1, aux1, locals = flatten_expr scope aux locals map in
        let idx1, aux2, locals = flatten_expr scope aux1 locals idx in
        Read (map1, idx1, pos), aux2, locals
    | Binder (b, vars, f, pos) as e ->
        let vars1, aux, locals =
          List.fold_right (fun v (vars1, aux, locals) ->
            match v with
            | GuardedVar (x, s) ->
                let s1, aux1, locals = flatten_expr scope aux locals s in
                GuardedVar (x, s) :: vars1, aux1, locals
            | _ -> v :: vars1, aux, locals)
            vars ([], aux, locals)
        in
        let f1, aux, locals = flatten_expr scope aux locals f in          
        (match b with
        | Exists | Forall -> Binder (b, vars1, f1, pos), aux, locals
        | SetComp ->
            let v_decl =
              match vars1 with
              | [UnguardedVar decl] -> decl
              | _ -> failwith "unexpected set comprehension"
            in
            let sc_id = GrassUtil.fresh_ident "set_compr" in
            let sc_locals = IdMap.add v_decl.v_name v_decl IdMap.empty in
            let fv = IdSet.elements (free_vars e) in
            let formals = List.filter (fun id -> IdMap.mem id locals) fv in
            let sc_locals =
              List.fold_left
                (fun sc_locals id -> IdMap.add id (IdMap.find id locals) sc_locals)
                sc_locals formals
            in
            let sc_decl =
              { pr_name = sc_id;
                pr_formals = formals;
                pr_outputs = [];
                pr_locals = sc_locals;
                pr_contracts = [];
                pr_body = Some e;
                pr_pos = pos;
              }
            in
            let actuals = List.map (fun id -> Ident (id, pos)) formals in
            let sc_app = PredApp (Pred sc_id, actuals, pos) in
            let aux_cmds, aux_funs = aux in
            sc_app, (aux_cmds, sc_decl :: aux_funs), locals
        )
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
        let args1, aux1, locals = flatten_expr_list scope aux locals args in
        let aux_var = Ident (aux_id, pos) in
        let call = Assign ([aux_var], [ProcCall (id, args1, pos)], pos) in
        let aux_cmds, aux_funs = aux1 in
        aux_var, (aux_cmds @ [call], aux_funs), locals
    | PredApp (p, args, pos) ->
        let args1, aux1, locals = flatten_expr_list scope aux locals args in
        PredApp(p, args1, pos), aux1, locals
    | UnaryOp (op, e, pos) ->
        let e1, aux1, locals = flatten_expr scope aux locals e in
        UnaryOp (op, e1, pos), aux1, locals
    | BinaryOp (e1, op, e2, ty, pos) ->
        let e21, aux1, locals = flatten_expr scope aux locals e2 in
        let e11, aux2, locals = flatten_expr scope aux1 locals e1 in
        BinaryOp (e11, op, e21, ty, pos), aux2, locals
    | Annot (e, PatternAnnot p, pos) ->
        let e1, aux1, locals = flatten_expr scope aux locals e in
        let p1, aux2, locals = flatten_expr scope aux1 locals p in
        Annot (e1, PatternAnnot p1, pos), aux2, locals
    | Annot (e, GeneratorAnnot (es, ge), pos) ->
        let es1, aux1, locals =
          List.fold_right (fun (e, id) (es1, aux1, locals) ->
            let e1, aux1, locals = flatten_expr scope aux locals e in
            (e1, id) :: es1, aux1, locals)
            es ([], aux, locals)
        in
        let ge1, aux2, locals = flatten_expr scope aux1 locals ge in
        let e1, aux3, locals = flatten_expr scope aux2 locals e in
        Annot (e1, GeneratorAnnot (es1, ge1), pos), aux3, locals
    | Annot (e, ann, pos) ->
        let e1, aux1, locals = flatten_expr scope aux locals e in
        Annot (e1, ann, pos), aux1, locals
    | e -> e, aux, locals
  in
  let rec flatten scope locals aux_funs returns = function
    | Skip pos -> Skip pos, locals, aux_funs
    | Block (stmts0, pos) ->
        let stmts, locals, aux_funs = 
          List.fold_left
            (fun (stmts, locals, aux_funs) stmt0  ->
              let stmt, locals, aux_funs = flatten pos locals aux_funs returns stmt0 in
              stmt :: stmts, locals, aux_funs
            ) 
            ([], locals, aux_funs) stmts0
        in Block (List.rev stmts, pos), locals, aux_funs
    | LocalVars (_, _, pos) ->
        failwith "flatten_exprs: LocalVars should have been eliminated"
    | Assume (e, pure, pos) ->
        let e1, aux1, locals = flatten_expr scope ([], aux_funs) locals e in
        Assume (e1, pure, pos), locals, snd aux1
    | Assert (e, pure, pos) ->
        let e1, aux1, locals = flatten_expr scope ([], aux_funs) locals e in
        Assert (e1, pure, pos), locals, snd aux1
    | Assign (lhs, [ProcCall (id, args, cpos)], pos) ->
        let args1, aux1, locals = flatten_expr_list scope ([], aux_funs) locals args in 
        begin
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
              let aux_cmds, aux_funs = aux1 in
              let assign_aux, locals, aux_funs =
                flatten scope locals aux_funs returns (Assign ([Read (map, idx, opos)], [aux_var], pos)) in
              mk_block pos (aux_cmds @ [Assign ([aux_var], [ProcCall (id, args1, cpos)], pos)] @ [assign_aux]), locals, aux_funs
          | _ ->
              let lhs1, aux2, locals = 
                List.fold_right 
                  (fun e (es, aux, locals) ->
                    let e1, aux1, locals = flatten_expr scope aux locals e in
                    e1 :: es, aux1, locals
                  ) 
                  lhs ([], aux1, locals)
              in
              let aux_cmds, aux_funs = aux2 in
              mk_block pos (aux_cmds @ [Assign (lhs1, [ProcCall (id, args1, cpos)], pos)]), locals, aux_funs
        end
    | Assign (lhs, rhs, pos) ->
        let rhs1, aux1, locals = flatten_expr_list scope ([], aux_funs) locals rhs in
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
                  let aux_cmds, aux_funs = aux1 in
                  Read (aux_var, ind, opos) :: es, (aux_cmds @ [assign_aux], aux_funs), locals
              | _ ->
                  e1 :: es, aux1, locals
            ) 
            lhs ([], aux1, locals)
        in
        let aux_cmds, aux_funs = aux2 in
        mk_block pos (aux_cmds @ [Assign (lhs1, rhs1, pos)]), locals, aux_funs
    | Dispose (e, pos) -> 
        let e1, aux, locals = flatten_expr scope ([], aux_funs) locals e in
        mk_block pos (fst aux @ [Dispose (e1, pos)]), locals, snd aux
    | Havoc (es, pos) -> 
        let es1, aux1, locals = flatten_expr_list scope ([], aux_funs) locals es in
        let aux_cmds, aux_funs = aux1 in
        mk_block pos (aux_cmds @ [Havoc (es1, pos)]), locals, aux_funs
    | If (cond, t, e, pos) ->
        let cond1, (aux_cmds, aux_funs), locals = flatten_expr scope ([], aux_funs) locals cond in
        let t1, locals, aux_funs = flatten scope locals aux_funs returns t in
        let e1, locals, aux_funs = flatten scope locals aux_funs returns e in
        mk_block pos (aux_cmds @ [If (cond1, t1, e1, pos)]), locals, aux_funs
    | Loop (inv, preb, cond, postb, pos) ->
        let inv1, aux_funs, locals = 
          List.fold_right
            (function Invariant (e, pos) -> fun (inv1, aux_funs, locals) ->
              let e1, (_, aux_funs), locals = flatten_expr scope ([], aux_funs) locals e in
              Invariant (e1, pos) :: inv1, aux_funs, locals)
            inv ([], aux_funs, locals)
        in
        let preb1, locals, aux_funs = flatten pos locals aux_funs returns preb in
        let cond1, (aux_cmds, aux_funs), locals = flatten_expr pos ([], aux_funs) locals cond in
        let postb1, locals, aux_funs = flatten pos locals aux_funs returns postb in
        Loop (inv, mk_block pos ([preb1] @ aux_cmds), cond1, postb1, pos), locals, aux_funs
    | Return ([ProcCall (id, args, cpos)], pos) ->
        let args1, aux1, locals = flatten_expr_list scope ([], aux_funs) locals args in
        let rts = List.map (fun id -> Ident (id, cpos)) returns in
        let assign = Assign (rts, [ProcCall (id, args1, cpos)], pos) in
        let ret = Return (rts, pos) in
        let aux_cmds, aux_funs = aux1 in
        mk_block pos (aux_cmds @ [assign; ret]), locals, aux_funs
    | Return (es, pos) ->
        let es1, (aux_cmds, aux_funs), locals = flatten_expr_list scope ([], aux_funs) locals es in
        mk_block pos (aux_cmds @ [Return (es1, pos)]), locals, aux_funs
  in
  let flatten_contracts aux_funs locals contracts =
    List.fold_right
      (fun c (contracts, aux_funs, locals) ->
        let flatten_spec e =
          let e1, (aux_cmds, aux_funs), locals =
            flatten_expr (pos_of_expr e) ([], aux_funs) locals e
          in
          match aux_cmds with
          | [] -> e1, aux_funs, locals
          | cmd :: _ -> illegal_side_effect_error (pos_of_stmt cmd) "specifications"
        in
        match c with
        | Requires (e, pure) -> 
            let e1, aux_funs, locals = flatten_spec e in
            Requires (e1, pure) :: contracts, aux_funs, locals
        | Ensures (e, pure) ->
            let e1, aux_funs, locals = flatten_spec e in
            Ensures (e1, pure) :: contracts, aux_funs, locals)
      contracts ([], aux_funs, locals)
  in
  let procs, aux_funs =
    IdMap.fold
      (fun _ decl (procs, aux_funs) ->
        let contracts, aux_funs, locals =
          flatten_contracts aux_funs decl.p_locals decl.p_contracts
        in
        let body, locals, aux_funs =
          flatten decl.p_pos locals aux_funs decl.p_returns decl.p_body
        in
        let decl1 =
          { decl with
            p_locals = locals;
            p_contracts = contracts;
            p_body = body }
        in
        IdMap.add decl.p_name decl1 procs, aux_funs)
      cu.proc_decls (IdMap.empty, [])
  in
  let preds, aux_funs =
    IdMap.fold
      (fun _ decl (preds, aux_funs) ->
        let contracts, aux_funs, locals =
          flatten_contracts aux_funs decl.pr_locals decl.pr_contracts
        in
        let body, (aux_cmds, aux_funs), locals =
          match decl.pr_body with
          | Some body ->
              let body, aux, locals = flatten_expr decl.pr_pos ([], aux_funs) decl.pr_locals body in
              Some body, aux, locals
          | None -> None, ([], aux_funs), locals
        in
        match aux_cmds with
        | cmd :: _ ->
            illegal_side_effect_error (pos_of_stmt cmd) "function and procedure bodies"
        | _ -> ();
        let decl1 =
          { decl with
            pr_locals = locals;
            pr_contracts = contracts;
            pr_body = body  
          }
        in
        IdMap.add decl.pr_name decl1 preds, aux_funs)
      cu.pred_decls (IdMap.empty, aux_funs)
  in
  let preds_all = List.fold_left (fun preds_all decl -> IdMap.add decl.pr_name decl preds_all) preds aux_funs in
  { cu with proc_decls = procs; pred_decls = preds_all }

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
        let rtype =
          match pred.pr_outputs with
          | [res_id] ->
              (IdMap.find res_id pred.pr_locals).v_type
          | _ -> PermType
        in
        let contracts =
          List.map (function
            | Requires (e, pure) -> Requires (check_spec pred.pr_locals pure e, pure)
            | Ensures (e, pure) -> Ensures (check_spec pred.pr_locals pure e, pure)) pred.pr_contracts
        in
        let body =
          Opt.map (infer_types cu pred.pr_locals rtype) pred.pr_body
        in
        let pred1 =
          { pred with
            pr_contracts = contracts;
            pr_body = body
          }
        in
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

(** Check compilation unit [cu]. *)
let check cu =
  let cu1 = resolve_names cu in
  let cu2 = infer_types cu1 in
  let cu3 = flatten_exprs cu2 in
  cu3
