open Form
open Programs
open SplSyntax


let resolve_names cus =
  let lookup_id init_id tbl pos =
    let name = FormUtil.name init_id in
    match SymbolTbl.find tbl name with
    | Some id -> id
    | None -> ProgError.error pos ("Unknown identifier " ^ name ^ ".")
  in 
  let check_struct id structs pos =
    if not (IdMap.mem id structs) then
      ProgError.error pos ("Identifier " ^ FormUtil.name id ^ " does not refer to a struct.")
  in
  let check_proc id procs pos =
    if not (IdMap.mem id procs) then
      ProgError.error pos ("Identifier " ^ FormUtil.name id ^ " does not refer to a procedure or predicate.")
  in
  let check_pred id preds pos =
    if not (IdMap.mem id preds) then
      ProgError.error pos ("Identifier " ^ FormUtil.name id ^ " does not refer to a procedure or predicate.")
  in
  let check_field id globals pos =
    let error () = 
      ProgError.error pos ("Identifier " ^ FormUtil.name id ^ " does not refer to a struct field.")
    in
    try 
      let decl = IdMap.find id globals in
      match decl.v_type with
      | FieldType _ -> ()
      | _ -> error ()
    with Not_found -> error ()
  in
  let declare_name pos init_id tbl =
    let name = FormUtil.name init_id in
    if SymbolTbl.declared_in_current tbl name then
      ProgError.error pos ("Redeclaration of identifier " ^ name ^ ".");
    let id = FormUtil.fresh_ident name in
    (id, SymbolTbl.add tbl name id)
  in
  let declare_var structs decl tbl =
    let id, tbl = declare_name decl.v_pos decl.v_name tbl in
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
  let rn cu (cus, tbl) =
    (* declare struct names *)
    let structs0, tbl =
      IdMap.fold 
        (fun init_id decl (structs, tbl) ->
          let id, tbl = declare_name decl.s_pos init_id tbl in
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
                let id, tbl = declare_name fdecl.v_pos init_id tbl in
                let res_type = match fdecl.v_type with
                | StructType init_id ->
                    let id = lookup_id init_id tbl fdecl.v_pos in
                    check_struct id structs0 fdecl.v_pos;
                    StructType id
                | ty -> ty
                in
                let fdecl = 
                  { fdecl with 
                    v_name = id; 
                    v_type = FieldType (decl.s_name, res_type) 
                  }
                in
                IdMap.add id fdecl fields, IdMap.add id fdecl globals, tbl
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
        let id, tbl = declare_name decl.p_pos init_id tbl in
        IdMap.add id { decl with p_name = id } procs, tbl)
        cu.proc_decls (IdMap.empty, tbl)
    in
    (* declare predicate names *)
    let preds0, tbl =
      IdMap.fold (fun init_id decl (preds, tbl) ->
        let id, tbl = declare_name decl.pr_pos init_id tbl in
        IdMap.add id { decl with pr_name = id } preds, tbl)
        cu.pred_decls (IdMap.empty, tbl)
    in
    let resolve_expr locals tbl e = 
      let rec re = function
        | New (init_id, pos) ->
            let id = lookup_id init_id tbl pos in
            check_struct id structs pos;
            New (id, pos)
        | Dot (e, init_id, pos) ->
            let id = lookup_id init_id tbl pos in
            check_field id globals pos;
            Dot (re e, id, pos)
        | Call (init_id, args, pos) ->
            let id = lookup_id init_id tbl pos in
            let args1 = List.map re args in
            (try 
              check_proc id procs0 pos;
              Call (id, args1, pos)
            with ProgError.Prog_error _ ->
              check_pred id preds0 pos;
              Pred (id, args1, pos))
        | Pred (init_id, args, pos) ->
            let id = lookup_id init_id tbl pos in
            check_pred id preds0 pos;
            Pred (id, List.map re args, pos)              
        | UnaryOp (op, e, pos) ->
            UnaryOp (op, re e, pos)
        | BinaryOp (e1, op, e2, pos) ->
            BinaryOp (re e1, op, re e2, pos)
        | Ident (init_id, pos) ->
            let id = lookup_id init_id tbl pos in
            Ident (id, pos)
        | e -> e
      in
      re e
    in
    let rec resolve_stmt locals tbl = function
      | Skip -> Skip, locals, tbl
      | Block (stmts0, pos) ->
        let stmts, locals, _ = 
          List.fold_left
            (fun (stmts, locals, tbl) stmt0  ->
              let stmt, locals, tbl = resolve_stmt locals tbl stmt0 in
              stmt :: stmts, locals, tbl
            ) 
            ([], locals, SymbolTbl.push tbl) stmts0
        in Block (List.rev stmts, pos), locals, tbl
      | LocalVars (vars, pos) ->
          let locals, tbl = List.fold_right 
              (fun decl (locals, tbl) ->
                let decl, tbl = declare_var structs decl tbl in
                IdMap.add decl.v_name decl locals, tbl
              )
              vars (locals, tbl)
          in
          Skip, locals, tbl
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
      | Return (ret_opt, pos) ->
          Return (Util.optmap (resolve_expr locals tbl) ret_opt, pos), locals, tbl
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
          let decl1 = { decl with p_locals = locals; p_contracts = contracts; p_body = body } in
          IdMap.add decl.p_name decl1 procs
        )
        procs0 IdMap.empty 
    in
    let preds =
      IdMap.fold
        (fun _ decl preds ->
          let locals, tbl = declare_vars decl.pr_locals structs (SymbolTbl.push tbl) in
          let body = resolve_expr locals tbl decl.pr_body in
          let decl1 = { decl with pr_locals = locals; pr_body = body } in
          IdMap.add decl.pr_name decl1 preds
        )
        preds0 IdMap.empty 
    in
    { cu with 
      var_decls = globals; 
      struct_decls = structs; 
      proc_decls = procs;
      pred_decls = preds;
    } :: cus, 
    tbl
  in
  let cus, _ = List.fold_right rn cus ([], SymbolTbl.empty) in
  cus


let flatten_exprs cus =
  let decl_aux_var name vtype pos locals =
    let aux_id = FormUtil.fresh_ident name in
    let decl = 
      { v_name = aux_id;
        v_type = vtype;
        v_ghost = false;
        v_aux = true;
        v_pos = pos;
      }
    in
    let locals1 = IdMap.add aux_id decl locals in
    aux_id, locals1
  in
  let rec check_side_effects = function
    | e -> ()
  in
  let fe cu =
    let rec flatten_expr aux locals = function
      | New (id, pos) as e ->
          let aux_id, locals1 = decl_aux_var "tmp" (StructType id) pos locals in
          let aux_var = Ident (aux_id, pos) in
          let alloc = Assign ([aux_var], [e], pos) in
          aux_var, alloc :: aux, locals1
      | Dot (e, id, pos) ->
          let e1, aux1, locals1 = flatten_expr aux locals e in
          Dot (e1, id, pos), aux1, locals1
      | Call (id, args, pos) ->
          let pdecl = IdMap.find id cu.proc_decls in
          let res_type = 
            match pdecl.p_returns with
            | [res] ->
                let rdecl = IdMap.find res pdecl.p_locals in
                rdecl.v_type
            | _ ->
                ProgError.error pos ("Procedure " ^ fst pdecl.p_name ^ " has more than one return value")
          in
          let aux_id, locals1 = decl_aux_var "tmp" res_type pos locals in
          let args1, aux1, locals1 = 
            List.fold_right 
              (fun arg (args1, aux1, locals1) ->
                let arg1, aux1, locals1 = flatten_expr aux1 locals1 arg in
                arg1 :: args1, aux1, locals1
              ) args ([], aux, locals)
          in
          let aux_var = Ident (aux_id, pos) in
          let call = Assign ([aux_var], [Call (id, args1, pos)], pos) in
          aux_var, (aux1 @ [call]), locals1 
      | Pred (init_id, args, pos) as e->
          List.iter check_side_effects args;
          e, aux, locals
      | UnaryOp (op, e, pos) ->
          let e1, aux1, locals1 = flatten_expr aux locals e in
          UnaryOp (op, e1, pos), aux1, locals1
      | BinaryOp (e1, op, e2, pos) ->
          let e21, aux1, locals1 = flatten_expr aux locals e2 in
          let e11, aux2, locals2 = flatten_expr aux1 locals1 e1 in
          BinaryOp (e11, op, e21, pos), aux2, locals2
      | e -> e, aux, locals
    in
    let rec flatten locals = function
      | Skip -> Skip, locals
      | Block (stmts0, pos) ->
        let stmts, locals = 
          List.fold_left
            (fun (stmts, locals) stmt0  ->
              let stmt, locals = flatten locals stmt0 in
              stmt :: stmts, locals
            ) 
            ([], locals) stmts0
        in Block (List.rev stmts, pos), locals
      | LocalVars (vars, pos) ->
          failwith "flatten_exprs: LocalVars should have been eliminated"
      | (Assume (e, pos) as stmt)
      | (Assert (e, pos) as stmt) ->
          check_side_effects e;
          stmt, locals
      | Assign (lhs, rhs, pos) ->
          let rhs1, aux1, locals1 = 
            List.fold_right 
              (fun e (es, aux, locals) ->
                let e1, aux1, locals1 = flatten_expr aux locals e in
                e1 :: es, aux1, locals1
              ) 
              rhs ([], [], locals)
          in 
          let lhs1, aux2, locals2 = 
            List.fold_right 
              (fun e (es, aux, locals) ->
                let e1, aux1, locals1 = flatten_expr aux locals e in
                e1 :: es, aux1, locals1
              ) 
              lhs ([], aux1, locals1)
          in 
          mk_block pos (aux2 @ [Assign (lhs1, rhs1, pos)]), locals1
      | Dispose (e, pos) -> 
          let e1, aux, locals1 = flatten_expr [] locals e in
          mk_block pos (aux @ [Dispose (e1, pos)]), locals
      | If (cond, t, e, pos) ->
          let cond1, aux, locals1 = flatten_expr [] locals cond in
          let t1, locals2 = flatten locals1 t in
          let e1, locals3 = flatten locals2 e in
          mk_block pos (aux @ [If (cond1, t1, e1, pos)]), locals3
      | Loop (inv, preb, cond, postb, pos) ->
          let _ = 
            List.iter 
              (function Invariant e -> check_side_effects e)
              inv
          in
          let preb1, locals1 = flatten locals preb in
          let cond1, aux, locals2 = flatten_expr [] locals1 cond in
          let postb1, locals3 = flatten locals2 postb in
          Loop (inv, mk_block pos ([preb1] @ aux), cond1, postb1, pos), locals
      | Return (ret_opt, pos) ->
          let ret_opt1, aux, locals1 =
            match ret_opt with
            | Some e -> 
                let e1, aux, locals1 = flatten_expr [] locals e in
                Some e1, aux, locals1
            | None -> None, [], locals
          in
          mk_block pos (aux @ [Return (ret_opt1, pos)]), locals1
    in
    let procs =
      IdMap.fold
        (fun _ decl procs ->
          let body, locals = flatten decl.p_locals decl.p_body in
          let decl1 = { decl with p_locals = locals; p_body = body } in
          IdMap.add decl.p_name decl1 procs)
        cu.proc_decls IdMap.empty
    in
    { cu with proc_decls = procs }
  in
  let cus = List.map fe cus in
  cus

let convert cus =
  let convert_cu cu prog =
    prog
  in
  List.fold_right convert_cu cus empty_prog

