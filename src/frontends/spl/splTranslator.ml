open Prog
open Sl
open Grass
open SplSyntax
open SplTypeChecker

let pred_arg_mismatch_error pos name expected =
    ProgError.error pos (Printf.sprintf "Predicate %s expects %d argument(s)" name expected)

let resolve_names cu =
  let lookup_id init_id tbl pos =
    let name = GrassUtil.name init_id in
    match SymbolTbl.find tbl name with
    | Some (id, _) -> id
    | None -> ProgError.error pos ("Unknown identifier " ^ name ^ ".")
  in 
  let check_struct id structs pos =
    if not (IdMap.mem id structs) then
      ProgError.error pos 
        ("Identifier " ^ GrassUtil.name id ^ " does not refer to a struct.")
  in
  let check_proc id procs pos =
    if not (IdMap.mem id procs) then
      ProgError.error pos 
        ("Identifier " ^ GrassUtil.name id ^ " does not refer to a procedure or predicate.")
  in
  let check_pred id preds pos =
    if not (IdMap.mem id preds) then
      ProgError.error pos 
        ("Identifier " ^ GrassUtil.name id ^ " does not refer to a procedure or predicate.")
  in
  let check_field id globals pos =
    let error () = 
      ProgError.error pos 
        ("Identifier " ^ GrassUtil.name id ^ " does not refer to a struct field.")
    in
    try 
      let decl = IdMap.find id globals in
      match decl.v_type with
      | FieldType _ -> ()
      | _ -> error ()
    with Not_found -> error ()
  in
  let declare_name pos init_id scope tbl =
    let name = GrassUtil.name init_id in
    match SymbolTbl.find_local tbl name with
    | Some _ -> 
        ProgError.error pos ("Identifier " ^ name ^ " has already been declared in this scope.")
    | None ->
        let id = 
          if init_id = Prog.alloc_id then alloc_id
          else GrassUtil.fresh_ident name 
        in
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
              let fdecl = { fdecl with v_name = id; v_type = res_type } in
              let gfdecl = { fdecl with v_type = FieldType (decl.s_name, res_type) } in
              IdMap.add id fdecl fields, IdMap.add id gfdecl globals, tbl
            )
            decl.s_fields (IdMap.empty, globals, tbl)
        in
        IdMap.add id { decl with s_fields = fields } structs, globals, tbl
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
    let rec re tbl = function
      | Setenum (ty, args, pos) ->
          let args1 = List.map (re tbl) args in
          Setenum (ty, args1, pos)
      | New (init_id, pos) ->
          let id = lookup_id init_id tbl pos in
          check_struct id structs pos;
          New (id, pos)
      | Dot (e, init_id, pos) ->
          let id = lookup_id init_id tbl pos in
          check_field id globals pos;
          Dot (re tbl e, id, pos)
      | GuardedQuant (q, init_id, e, f, pos) ->
          let e1 = re tbl e in
          let id, tbl1 = declare_name pos init_id pos tbl in
          let f1 = re tbl1 f in
          GuardedQuant (q, id, e1, f1, pos)
      | Quant (q, vars, f, pos) ->
          let decls, tbl1 = List.fold_right 
              (fun decl (decls, tbl) ->
                let decl, tbl1 = declare_var structs decl tbl in
                decl :: decls, tbl1
              ) 
              vars ([], tbl)
          in
          let f1 = re tbl1 f in
          Quant (q, decls, f1, pos)
      | ProcCall (("acc", _), [arg], pos) ->
          Access (re tbl arg, pos)
      | ProcCall (("Btwn", _), args, pos) ->
          let args1 = List.map (re tbl) args in
          (match args1 with
          | [fld; x; y; z] ->
              BtwnPred (fld, x, y, z, pos)
          | _ -> pred_arg_mismatch_error pos "Btwn" 4)
      | ProcCall (init_id, args, pos) ->
          let id = lookup_id init_id tbl pos in
          let args1 = List.map (re tbl) args in
          (try 
            check_proc id procs0 pos;
            ProcCall (id, args1, pos)
          with ProgError.Prog_error _ ->
            check_pred id preds0 pos;
            PredApp (id, args1, pos))
      | PredApp (init_id, args, pos) ->
          let id = lookup_id init_id tbl pos in
          check_pred id preds0 pos;
          PredApp (id, List.map (re tbl) args, pos)              
      | UnaryOp (op, e, pos) ->
          UnaryOp (op, re tbl e, pos)
      | BinaryOp (e1, op, e2, pos) ->
          BinaryOp (re tbl e1, op, re tbl e2, pos)
      | Ident (init_id, pos) ->
          let id = lookup_id init_id tbl pos in
          Ident (id, pos)
      | Annot (e, GeneratorAnnot (es, ge), pos) ->
          let es1 = List.map (re tbl) es in
          Annot (re tbl e, GeneratorAnnot (es1, re tbl ge), pos)
      | Annot (e, ann, pos) ->
          Annot (re tbl e, ann, pos)
      | e -> e
    in
    re tbl e
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
        let es_opt1, _ =
          (* ignore computed types of initializers for now... *)
          match es_opt with
          | Some es ->
              let es1, tys = 
                List.split 
                  (List.map (fun e -> 
                    let e1 = resolve_expr locals tbl e in
                    e1, type_of_expr cu locals e1) es)
              in
              Some es1, tys
          | None ->
              None, List.map (fun decl -> decl.v_type) vars
        in
        let ids, locals, tbl = 
          List.fold_right
            (fun decl (ids, locals, tbl) ->
              let decl, tbl = declare_var structs decl tbl in
              Ident (decl.v_name, decl.v_pos) :: ids, 
              IdMap.add decl.v_name decl locals, 
              tbl
            )
            vars ([], locals, tbl)
        in
        (match es_opt1 with
        | Some es1 -> 
            Assign (ids, es1, pos), locals, tbl
        | None -> 
            Havoc (ids, pos), locals, tbl)
    | Assume (e, pos) ->
        Assume (resolve_expr locals tbl e, pos), locals, tbl
    | Assert (e, pos) ->
        Assert (resolve_expr locals tbl e, pos), locals, tbl
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
            (function Invariant e -> fun inv1 ->
              Invariant (resolve_expr locals tbl e) :: inv1
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
        let locals0, tbl = declare_vars decl.p_locals structs (SymbolTbl.push tbl) in
        let contracts = 
          List.map 
            (function 
              | Requires e -> Requires (resolve_expr locals0 tbl e)
              | Ensures e -> Ensures (resolve_expr locals0 tbl e)
            )
            decl.p_contracts
        in
        let body, locals, _ = resolve_stmt locals0 tbl decl.p_body in
        let formals = List.map (fun id -> lookup_id id tbl decl.p_pos) decl.p_formals in
        let returns = List.map (fun id -> lookup_id id tbl decl.p_pos) decl.p_returns in
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
        let outputs = List.map (fun id -> lookup_id id tbl decl.pr_pos) decl.pr_outputs in
        let decl1 = 
          { decl with 
            pr_formals = formals; 
            pr_outputs = outputs; 
            pr_locals = locals; 
            pr_body = body 
          } 
        in
        IdMap.add decl.pr_name decl1 preds
      )
      preds0 IdMap.empty 
  in
  { cu with 
    var_decls = globals; 
    struct_decls = structs; 
    proc_decls = procs;
    pred_decls = preds;
  }

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
  let fe cu =
    let rec flatten_expr scope aux locals = function
      | Setenum (ty, args, pos) as e ->
          List.iter check_side_effects args;
          e, aux, locals
      | New (id, pos) as e ->
          let aux_id, locals = decl_aux_var "tmp" (StructType id) pos scope locals in
          let aux_var = Ident (aux_id, pos) in
          let alloc = Assign ([aux_var], [e], pos) in
          aux_var, alloc :: aux, locals
      | Dot (e, id, pos) ->
          let e1, aux1, locals = flatten_expr scope aux locals e in
          Dot (e1, id, pos), aux1, locals
      | Quant (q, _, f, pos) as e ->
          check_side_effects f;
          e, aux, locals
      | GuardedQuant (q, id, s, f, pos) as e ->
          check_side_effects s;
          check_side_effects f;
          e, aux, locals
      | ProcCall (id, args, pos) ->
          let pdecl = IdMap.find id cu.proc_decls in
          let res_type = 
            match pdecl.p_returns with
            | [res] ->
                let rdecl = IdMap.find res pdecl.p_locals in
                rdecl.v_type
            | _ ->
                ProgError.error pos 
                  ("Procedure " ^ fst pdecl.p_name ^ " has more than one return value")
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
      | BinaryOp (e1, op, e2, pos) ->
          let e21, aux1, locals = flatten_expr scope aux locals e2 in
          let e11, aux2, locals = flatten_expr scope aux1 locals e1 in
          BinaryOp (e11, op, e21, pos), aux2, locals
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
      | (Assume (e, pos) as stmt)
      | (Assert (e, pos) as stmt) ->
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
            | [Dot (e, id, opos)] ->
                let decl = IdMap.find id cu.var_decls in
                let res_ty = 
                  match decl.v_type with
                  | FieldType (_, ty) -> ty
                  | ty -> ty
                in
                let aux_id, locals = decl_aux_var "tmp" res_ty opos scope locals in
                let aux_var = Ident (aux_id, pos) in
                let assign_aux = Assign ([Dot (e, id, opos)], [aux_var], pos) in
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
              (function Invariant e -> check_side_effects e)
              inv
          in
          let preb1, locals = flatten pos locals returns preb in
          let cond1, aux, locals2 = flatten_expr pos [] locals cond in
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
  in
  fe cu

type cexpr =
  | SL_form of Sl.form
  | FOL_form of Grass.form
  | FOL_term of Grass.term * typ

(*
let rec compatible_types ty1 ty2 =
  match ty1, ty2 with
  | StructType _, NullType
  | NullType, StructType _ 
  | IntType, IntType
  | BoolType, BoolType -> true
  | StructType id1, StructType id2 when id1 = id2 -> true
  | FieldType (id1, ty1), FieldType (ty2 -> compatible_types ty1 ty2
  | _, _ -> false*)

let convert cu =
    let find_var_decl locals id =
      try IdMap.find id locals 
      with Not_found -> 
        try IdMap.find id cu.var_decls
        with Not_found -> failwith ("Unable to find identifier " ^ (string_of_ident id))
    in
    let field_type pos id fld_id =
      let decl = IdMap.find id cu.struct_decls in
      try 
        let fdecl = IdMap.find fld_id decl.s_fields in
        fdecl.v_type
      with Not_found ->
        ProgError.error pos 
          ("Struct " ^ fst id ^ " does not have a field named " ^ fst fld_id)
    in
    let rec convert_type = function
      | LocType -> Loc
      | StructType id -> Loc
      | FieldType (id, typ) -> GrassUtil.field_sort (convert_type typ) 
      | SetType typ -> Set (convert_type typ)
      | IntType -> Int
      | BoolType -> Bool
      | UniversalType -> failwith "cannot convert universal type"
    in
    let convert_var_decl decl = 
      { var_name = decl.v_name;
        var_orig_name = fst decl.v_name;
        var_sort = convert_type decl.v_type;
        var_is_ghost = decl.v_ghost;
        var_is_implicit = decl.v_implicit;
        var_is_aux = decl.v_aux;
        var_pos = decl.v_pos;
        var_scope = decl.v_scope;
      }
    in 
    let ty_str = function
      | LocType -> "expression of a struct type"
      | StructType id -> "expression of type " ^ (fst id)
      | SetType _ -> "expression of type set"
      | IntType -> "expression of type int"
      | BoolType -> "expression of type bool"
      | FieldType _ -> "field"
      | UniversalType -> "expression"
    in
    let type_error pos expected found =
      ProgError.type_error pos
        ("Expected an " ^ expected ^ " but found an " ^ found)
    in
    let rec convert_expr locals = function
      | Null _ -> FOL_term (GrassUtil.mk_null, LocType)
      | Emp _ -> SL_form SlUtil.mk_emp
      | Setenum (ty, es, pos) ->
          let ts, ty = 
            List.fold_right (fun e (ts, ty) ->
              let t, ty = extract_term locals ty e in
              t :: ts, ty)
              es ([], ty)
          in
          let elem_ty =  convert_type ty in
          (match es with
          | [] -> FOL_term (GrassUtil.mk_empty (Set elem_ty), SetType ty)
          | _ -> FOL_term (GrassUtil.mk_setenum ts, SetType ty))
      | IntVal (i, _) -> FOL_term (GrassUtil.mk_int i, IntType)
      | BoolVal (b, pos) -> FOL_form (GrassUtil.mk_srcpos pos (GrassUtil.mk_bool b))
      | Dot (e, fld_id, pos) -> 
          let t, ty = extract_term locals LocType e in
          (match ty with
          | StructType id ->
              let res_ty = field_type pos id fld_id in
              let res_srt = convert_type res_ty in
              let fld = GrassUtil.mk_free_const (GrassUtil.field_sort res_srt) fld_id in
              FOL_term (GrassUtil.mk_read fld t, res_ty)
          | LocType -> ProgError.error pos "Cannot dereference null"
          | ty -> failwith "unexpected type")
      | Access (e, pos) ->
          let t, ty = extract_term locals UniversalType e in
          (match ty with
          | StructType id ->
              SL_form (SlUtil.mk_cell ~pos:pos t)
          | SetType (StructType _) ->
              SL_form (SlUtil.mk_region ~pos:pos t)
          | LocType -> ProgError.error pos "Cannot access null"
          | ty -> failwith "unexpected type")
      | BtwnPred (fld, x, y, z, pos) ->
          let tfld, fld_ty = extract_term locals UniversalType fld in
          (match fld_ty with
          | FieldType (id, StructType id1) when id = id1 ->
              let tx, _ = extract_term locals (StructType id) x in
              let ty, _ = extract_term locals (StructType id) y in
              let tz, _ = extract_term locals (StructType id) z in
              FOL_form (GrassUtil.mk_srcpos pos (GrassUtil.mk_btwn tfld tx ty tz))
          | _ -> type_error (pos_of_expr fld) "reference field" (ty_str fld_ty))
      | Quant (q, decls, f, pos) ->
          let vars, locals1 = 
             List.fold_right (fun decl (vars, locals1) ->
               let id = decl.v_name in
               let ty = decl.v_type in
               (id, convert_type ty) :: vars, IdMap.add id decl locals1)
               decls ([], locals)
          in
          let subst = 
            List.fold_right (fun (id, srt) subst -> 
              IdMap.add id (GrassUtil.mk_var srt id) subst)
              vars IdMap.empty
          in            
          (try
            let mk_quant = match q with
	    | Forall -> GrassUtil.mk_forall
            | Exists -> GrassUtil.mk_exists
            in
            let f1 = extract_fol_form locals1 f in
            let f2 = GrassUtil.subst_consts subst f1 in
            FOL_form (GrassUtil.mk_srcpos pos (mk_quant vars f2))
          with _ -> 
            let mk_quant = match q with
            | Forall -> SlUtil.mk_forall 
            | Exists -> SlUtil.mk_exists
            in
            let f1 = extract_sl_form locals1 f in
            let f2 = SlUtil.subst_consts subst f1 in
            SL_form (mk_quant ~pos:pos vars f2))
      | GuardedQuant (q, id, e, f, pos) ->
          let e1, ty = extract_term locals (SetType UniversalType) e in
          (match ty with
          | SetType elem_srt ->
              let decl = var_decl id elem_srt false false pos pos in
              let locals1 = IdMap.add id decl locals in
              let elem_srt = convert_type elem_srt in
              let v_id = GrassUtil.mk_var elem_srt id in
	      let mk_guard = match q with
	      | Forall -> GrassUtil.mk_implies
              | Exists -> fun f g -> GrassUtil.mk_and [f; g] 
	      in
              let mk_quant = match q with
	      | Forall -> GrassUtil.mk_forall
              | Exists -> GrassUtil.mk_exists
              in
              let f0, ann = 
                match extract_fol_form locals1 f with
                | Binder (_, [], f0, ann) -> f0, ann
                | f0 -> f0, []
              in
              let f1 = GrassUtil.annotate (mk_guard (GrassUtil.mk_elem v_id e1) f0) ann in
              let f2 = GrassUtil.subst_consts (IdMap.add id v_id IdMap.empty) f1 in
              FOL_form (GrassUtil.mk_srcpos pos (mk_quant [(id, elem_srt)] f2))
          | _ -> failwith "unexpected type")
      | PredApp (id, es, pos) ->
          let decl = IdMap.find id cu.pred_decls in
          let tys = List.map (fun p -> (IdMap.find p decl.pr_locals).v_type) decl.pr_formals in
          let ts = 
            if List.length es > List.length tys
            then pred_arg_mismatch_error pos (fst id) (List.length tys)
            else Util.map2 (extract_term locals) tys es
          in 
          (match decl.pr_outputs with
          | [] -> SL_form (SlUtil.mk_pred ~pos:pos id (List.map fst ts))
          | [res] ->
              let res_decl = IdMap.find res decl.pr_locals in
              let res_srt = convert_type res_decl.v_type in
              let t = GrassUtil.mk_free_fun res_srt id (List.map fst ts) in
              FOL_term (t, res_decl.v_type)
          | _ -> failwith "impossible")
      | BinaryOp (e1, OpEq, e2, pos) ->
          (match convert_expr locals e1 with
          | FOL_form _ 
          | FOL_term (_, BoolType) ->
              let f1 = extract_fol_form locals e1 in
              let f2 = extract_fol_form locals e2 in
              FOL_form (GrassUtil.mk_srcpos pos (GrassUtil.mk_iff f1 f2))
          | FOL_term (t1, ty1) ->
              let t2, _ = extract_term locals ty1 e2 in
              FOL_form (GrassUtil.mk_srcpos pos (GrassUtil.mk_eq t1 t2))
          | SL_form _ -> 
              ProgError.error (pos_of_expr e1) 
                "Operator == is not defined for SL formulas")
      | BinaryOp (e1, (OpDiff as op), e2, _)
      | BinaryOp (e1, (OpUn as op), e2, _)      
      | BinaryOp (e1, (OpInt as op), e2, _) ->
          let mk_app =
            match op with
            | OpDiff -> GrassUtil.mk_diff
            | OpUn -> (fun t1 t2 -> GrassUtil.mk_union [t1; t2])
            | OpInt -> (fun t1 t2 -> GrassUtil.mk_inter [t1; t2])
            | _ -> failwith "unexpected operator"
          in
          let t1, ty1 = extract_term locals (SetType UniversalType) e1 in
          let t2, ty2 = extract_term locals ty1 e2 in
          FOL_term (mk_app t1 t2, ty2)
      | BinaryOp (e1, OpNeq, e2, pos) ->
          convert_expr locals (UnaryOp (OpNot, BinaryOp (e1, OpEq, e2, pos), pos))
      | BinaryOp (e1, (OpMinus as op), e2, _)
      | BinaryOp (e1, (OpPlus as op), e2, _)
      | BinaryOp (e1, (OpMult as op), e2, _)
      | BinaryOp (e1, (OpDiv as op), e2, _) ->
          let mk_app =
            match op with
            | OpMinus -> GrassUtil.mk_minus
            | OpPlus -> GrassUtil.mk_plus
            | OpMult -> GrassUtil.mk_mult
            | OpDiv -> GrassUtil.mk_div
            | _ -> failwith "unexpected operator"
          in
          let t1, _ = extract_term locals IntType e1 in
          let t2, _ = extract_term locals IntType e2 in
          FOL_term (mk_app t1 t2, IntType)
      | BinaryOp (e1, (OpGt as op), e2, pos)
      | BinaryOp (e1, (OpLt as op), e2, pos)
      | BinaryOp (e1, (OpGeq as op), e2, pos)
      | BinaryOp (e1, (OpLeq as op), e2, pos) ->
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
          (try
            let t1, _ = extract_term locals IntType e1 in
            let t2, _ = extract_term locals IntType e2 in            
            FOL_form (GrassUtil.mk_srcpos pos (mk_int_form t1 t2))
          with _ ->
            let t1, ty1 = extract_term locals (SetType UniversalType) e1 in
            let t2, _ = extract_term locals ty1 e2 in            
            FOL_form (GrassUtil.mk_srcpos pos (mk_set_form t1 t2)))
      | BinaryOp (e1, OpIn, e2, pos) ->
          let t1, ty1 = extract_term locals UniversalType e1 in
          let t2, _ = extract_term locals (SetType ty1) e2 in
          FOL_form (GrassUtil.mk_srcpos pos (GrassUtil.mk_elem t1 t2))
      | BinaryOp (e1, (OpAnd as op), e2, _)
      | BinaryOp (e1, (OpOr as op), e2, _)
      | BinaryOp (e1, (OpImpl as op), e2, _) ->
          (try
            let mk_form = 
              match op with
              | OpAnd -> fun f1 f2 -> GrassUtil.mk_and [f1; f2]
              | OpOr -> fun f1 f2 -> GrassUtil.mk_or [f1; f2]
              | OpImpl -> GrassUtil.mk_implies           
              | _ -> failwith "unexpected operator"
            in
            let f1 = extract_fol_form locals e1 in
            let f2 = extract_fol_form locals e2 in
            FOL_form (mk_form f1 f2)
          with ProgError.Prog_error _ ->
            let mk_form = 
              match op with
              | OpAnd -> SlUtil.mk_and
              | OpOr -> SlUtil.mk_or
              | OpImpl -> SlUtil.mk_implies
              | _ -> failwith "unexpected operator"      
            in
            let f1 = extract_sl_form locals e1 in
            let f2 = extract_sl_form locals e2 in
            SL_form (mk_form f1 f2))
      | BinaryOp (e1, OpPts, e2, pos) ->
          let fld, ind, ty = 
            match convert_expr locals e1 with
            | FOL_term (App (Read, [fld; ind], _), ty) -> fld, ind, ty
            | _ -> 
                ProgError.error (pos_of_expr e1) 
                  "Expected field access on left-hand-side of points-to predicate"
          in
          let t2, _ = extract_term locals ty e2 in
          SL_form (SlUtil.mk_pts ~pos:pos fld ind t2)
      | BinaryOp (e1, (OpSepStar as op), e2, pos)
      | BinaryOp (e1, (OpSepPlus as op), e2, pos)
      | BinaryOp (e1, (OpSepIncl as op), e2, pos) ->
          let mk_op = function
            | OpSepStar -> SlUtil.mk_sep_star
            | OpSepPlus -> SlUtil.mk_sep_plus
            | OpSepIncl -> SlUtil.mk_sep_incl
            | _ -> failwith "unexpected operator"
          in
          let f1 = extract_sl_form locals e1 in
          let f2 = extract_sl_form locals e2 in
          SL_form (mk_op ~pos:pos op f1 f2)
      | UnaryOp (OpPlus, e, _) ->
          let t, _ = extract_term locals IntType e in 
          FOL_term (t, IntType)
      | UnaryOp (OpMinus, e, _) ->
          let t, _ = extract_term locals IntType e in
          FOL_term (GrassUtil.mk_uminus t, IntType)
      | UnaryOp (OpNot, e, pos) ->
          (try
            let f = extract_fol_form locals e in
            FOL_form (GrassUtil.mk_not f)
          with ProgError.Prog_error _ ->
            let f = extract_sl_form locals e in
            SL_form (SlUtil.mk_not ~pos:pos f))
      | Ident (id, pos) ->
          let decl = find_var_decl locals id in
          let srt = convert_type decl.v_type in
          FOL_term (GrassUtil.mk_free_const srt decl.v_name, decl.v_type)
      | Annot (e, CommentAnnot c, pos) ->
          let f = extract_fol_form locals e in
          FOL_form (GrassUtil.annotate f [Comment c])
      | Annot (e, GeneratorAnnot (es, ge), pos) ->
          let f = extract_fol_form locals e in
          let es1 = List.map (fun e -> fst (extract_term locals UniversalType e)) es in
          let ge1, _ = extract_term locals UniversalType ge in
          let gts = GrassUtil.ground_terms (Atom (ge1, [])) in
          let matches = 
            List.map (fun e -> 
              let ce = GrassUtil.free_consts_term e in
              let flt = 
                TermSet.fold 
                  (function 
                    | App (FreeSym sym, ts, _) ->
                        (function 
                          | FilterTrue ->
                              if List.exists 
                                  (function App (FreeSym id, [], _) -> IdSet.mem id ce | _ -> false) ts
                              then FilterNotOccurs (FreeSym sym)
                              else FilterTrue
                          | flt -> flt)
                    | _ -> function flt -> flt)
                  gts FilterTrue
              in
              Match (e, flt)) es1
          in
          FOL_form (GrassUtil.annotate f [TermGenerator ([], [], matches, ge1)])
      | _ -> failwith "convert_expr: unexpected expression"
    and extract_sl_form locals e =
      match convert_expr locals e with
      | SL_form f -> f
      | FOL_form f -> Pure (f, Some (pos_of_expr e))
      | FOL_term (t, ty) ->
         type_error (pos_of_expr e) "expression of type bool" (ty_str ty)
    and extract_fol_form locals e =
      match convert_expr locals e with
      | SL_form (Sl.Atom (Pred p, ts, pos)) ->
          GrassUtil.mk_pred ~ann:[SrcPos (pos_of_expr e)] p ts
      | SL_form _ ->
          type_error (pos_of_expr e) "expression of type bool" "SL formula"
      | FOL_form f -> f
      | FOL_term (t, BoolType) -> Grass.Atom (t, [SrcPos (pos_of_expr e)])
      | FOL_term (t, ty) -> type_error (pos_of_expr e) "expression of type bool" (ty_str ty)
    and extract_term locals ty e =
      match convert_expr locals e with
      | SL_form _ -> type_error (pos_of_expr e) (ty_str ty) "SL formula"
      | FOL_form (BoolOp (And, [])) 
      | FOL_form (Binder (_, [], BoolOp (And, []), _)) -> 
          Grass.App (BoolConst true, [], Bool), BoolType
      | FOL_form (BoolOp (Or, []))
      | FOL_form (Binder (_, [], BoolOp (Or, []), _)) -> 
          Grass.App (BoolConst false, [], Bool), BoolType
      | FOL_form (Atom (t, _)) -> t, BoolType
      | FOL_form _ -> type_error (pos_of_expr e) (ty_str ty) "formula"
      | FOL_term (t, tty) ->
          let rec match_types ty1 ty2 = 
            match ty1, ty2 with
            | LocType, StructType _
            | StructType _, LocType -> ty2
            | UniversalType, _ -> ty2
            | _, UniversalType -> ty1
            | SetType ty1, SetType ty2 -> SetType (match_types ty1 ty2)
            | ty, tty when ty = tty -> ty2
            | _ -> type_error (pos_of_expr e) (ty_str ty) (ty_str tty)
          in t, match_types ty tty
    in
    let convert_spec_form locals e name msg =
      let f = extract_sl_form locals e in
      mk_spec_form (SL f) name msg (pos_of_expr e)
    in
    let convert_loop_contract proc_name locals contract =
      List.map
        (function Invariant e -> 
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
          convert_spec_form locals e "invariant" (Some msg)
        )
        contract
    in
    let rec convert_stmt proc = 
      let convert_lhs es tys = 
        let ts = List.map2 (extract_term proc.p_locals) tys es in
        match ts with
        | [App (Read, [App (FreeSym fld, [], _); ind], _), _] -> [fld], Some ind
        | _ -> 
            let ids = 
              List.map 
                (function 
                  | Ident (id, _) -> id
                  | e -> 
                      ProgError.error (pos_of_expr e) 
                        "Only variables are allowed on left-hand-side of simultaneous assignments"
                ) es                
            in ids, None
      in
      function
      | Skip pos -> mk_seq_cmd [] pos
      | Block (stmts, pos) ->
          let cmds = List.map (convert_stmt proc) stmts in
          mk_seq_cmd cmds pos
      | Assume (e, pos) ->
          let sf = convert_spec_form proc.p_locals e "assume" None in
          mk_assume_cmd sf pos
      | Assert (e, pos) ->
          let sf = convert_spec_form proc.p_locals e "assert" None in
          mk_assert_cmd sf pos
      | Assign (lhs, [ProcCall (id, es, cpos)], pos) ->
          let decl = IdMap.find id cu.proc_decls in
          let formals = List.filter (fun p -> not (IdMap.find p decl.p_locals).v_implicit) decl.p_formals in
          let formal_tys = List.map (fun p -> (IdMap.find p decl.p_locals).v_type) formals in
          let return_tys = List.map (fun p -> (IdMap.find p decl.p_locals).v_type) decl.p_returns in
          let args = 
            try List.map2 (fun ty e -> fst (extract_term proc.p_locals ty e)) formal_tys es
            with Invalid_argument _ -> 
              ProgError.error cpos 
                (Printf.sprintf "Procedure %s expects %d argument(s)" 
                   (fst id) (List.length formal_tys))
          in 
          let lhs_ids, _ = 
            try convert_lhs lhs return_tys
            with Invalid_argument _ ->
              ProgError.error pos
              (Printf.sprintf "Procedure %s has %d return value(s)" 
                 (fst id) (List.length return_tys))
          in
          mk_call_cmd lhs_ids id args cpos
      | Assign ([lhs], [New (id, npos)], pos) ->
          let lhs_ids, _ = convert_lhs [lhs] [StructType id] in
          let lhs_id = List.hd lhs_ids in
          let new_cmd = mk_new_cmd lhs_id Loc npos in
          new_cmd
      | Assign (lhs, rhs, pos) ->
          let rhs_ts, rhs_tys = 
            Util.map_split (fun e ->
              match convert_expr proc.p_locals e with
              | SL_form _ -> ProgError.error (pos_of_expr e) "SL formulas cannot be assigned"
              | FOL_term (t, ty) -> t, ty
              | FOL_form f -> 
                  extract_term proc.p_locals BoolType e)
              rhs
          in
          let lhs_ids, ind_opt =
            try convert_lhs lhs rhs_tys
            with Invalid_argument _ -> 
              ProgError.error pos 
                "Mismatch in number of expressions on left and right side of assignment"                
          in
          (match ind_opt with
          | Some t -> 
              let fld_srt = GrassUtil.field_sort (convert_type (List.hd rhs_tys)) in
              let fld = GrassUtil.mk_free_const fld_srt (List.hd lhs_ids) in
              mk_assign_cmd lhs_ids [GrassUtil.mk_write fld t (List.hd rhs_ts)] pos
          | None -> mk_assign_cmd lhs_ids rhs_ts pos)
      | Dispose (e, pos) ->
          let t, _ = extract_term proc.p_locals LocType e in
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
          let cond = extract_fol_form proc.p_locals c in
          let t_cmd = convert_stmt proc t in
          let e_cmd = convert_stmt proc e in
          let t_msg = "The 'then' branch of this conditional has been taken on the error trace" in
          let e_msg = "The 'else' branch of this conditional has been taken on the error trace" in
          mk_ite cond (pos_of_expr c) t_cmd e_cmd t_msg e_msg pos
      | Loop (contract, preb, cond, postb, pos) ->
          let preb_cmd = convert_stmt proc preb in
          let cond_pos = pos_of_expr cond in
          let cond = extract_fol_form proc.p_locals cond in
          let invs = convert_loop_contract proc.p_name proc.p_locals contract in
          let postb_cmd = convert_stmt proc postb in
          mk_loop_cmd invs preb_cmd cond cond_pos postb_cmd pos
      | Return (es, pos) ->
          let return_tys = List.map (fun p -> (IdMap.find p proc.p_locals).v_type) proc.p_returns in
          let ts = 
            try List.map2 (fun ty e -> fst (extract_term proc.p_locals ty e)) return_tys es
            with Invalid_argument _ -> 
              ProgError.error pos 
                (Printf.sprintf "Procedure %s returns %d values(s), found %d" 
                   (fst proc.p_name) (List.length return_tys) (List.length es))
          in
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
          let body = extract_fol_form decl.pr_locals decl.pr_body in
          let pred_decl = 
            { pred_name = id;
              pred_formals = decl.pr_formals;
              pred_outputs = decl.pr_outputs;
              pred_locals = IdMap.map convert_var_decl decl.pr_locals;
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
          | Requires e -> fun (pre, post) -> 
              let mk_msg caller =
                Printf.sprintf 
                  "A precondition for this call of %s might not hold"
                  (string_of_ident proc_name),
                ProgError.mk_error_info "This is the precondition that might not hold"
              in
              let name = "precondition of " ^ string_of_ident proc_name in
              convert_spec_form locals e name (Some mk_msg) :: pre, post
          | Ensures e -> fun (pre, post) ->
              let mk_msg caller =
                Printf.sprintf 
                  "A postcondition of procedure %s might not hold at this return point"
                  (string_of_ident proc_name),
                ProgError.mk_error_info "This is the postcondition that might not hold"
              in 
              let name = "postcondition of " ^ string_of_ident proc_name in
              pre, convert_spec_form locals e name (Some mk_msg) :: post)
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
           } 
          in
          declare_proc prog proc_decl
        )
        cu.proc_decls prog
    in
    prog

let to_program cu =
  let cu1 = resolve_names cu in
  let cu2 = flatten_exprs cu1 in
  convert cu2
