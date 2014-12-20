open Grass
open SplSyntax

let pred_arg_mismatch_error pos name expected =
  ProgError.error pos (Printf.sprintf "Predicate %s expects %d argument(s)" name expected)

let type_error pos exp_ty fnd_ty =
  let ty_str ty = "expression of type " ^ string_of_type ty in
  ProgError.type_error pos
    ("Expected an " ^ ty_str exp_ty ^ " but found an " ^ ty_str fnd_ty)

let match_types pos oty1 oty2 =
  let rec mt ty1 ty2 =
  match ty1, ty2 with
  | AnyRefType, StructType _ -> ty2
  | StructType _, AnyRefType -> ty1
  | AnyType, _ -> ty2
  | _, AnyType -> ty1
  | SetType ty1, SetType ty2 ->
      SetType (mt ty1 ty2)
  | MapType (dty1, rty1), MapType (dty2, rty2) ->
      let dty = mt dty1 dty2 in
      let rty = mt rty1 rty2 in
      MapType (dty, rty)
  | ty, tty when ty = tty -> ty2
  | _ -> type_error pos oty1 oty2
  in mt oty1 oty2

(** Computes SPL type of expression [e] in compilation unit [cu] and environment [locals].
  * Assumes that all identifiers in [e] have been resolved. *)
let type_of_expr cu locals e = 
  let rec te = function
    (* Bool return values *)
    | UnaryOp (OpNot, _, _)
    | BinaryOp (_, OpAnd, _, _, _)
    | BinaryOp (_, OpOr, _, _, _)
    | BinaryOp (_, OpImpl, _, _, _)
    | BinaryOp (_, OpEq, _, _, _)
    | BinaryOp (_, OpGt, _, _, _)
    | BinaryOp (_, OpLt, _, _, _)
    | BinaryOp (_, OpGeq, _, _, _)
    | BinaryOp (_, OpLeq, _, _, _)
    | BinaryOp (_, OpIn, _, _, _)
    | GuardedQuant _ 
    | Quant _
    | BtwnPred _
    | BoolVal _ -> BoolType
    (* Int return values *)
    | UnaryOp (OpMinus, _, _) 
    | BinaryOp (_, OpMinus, _, _, _)
    | BinaryOp (_, OpPlus, _, _, _)
    | BinaryOp (_, OpMult, _, _, _)
    | BinaryOp (_, OpDiv, _, _, _)
    | IntVal _ -> IntType
    (* Set return values *)
    | BinaryOp (e, OpDiff, _, _, _)
    | BinaryOp (e, OpUn, _, _, _)
    | BinaryOp (e, OpInt, _, _, _) ->
        te e
    | Setenum (ty, _, _) ->
        SetType ty
    (* Permission types *)
    | BinaryOp (_, OpSepStar, _, _, _)
    | BinaryOp (_, OpSepPlus, _, _, _)
    | BinaryOp (_, OpPts, _, _, _)
    | BinaryOp (_, OpSepIncl, _, _, _)
    | Access _
    | Emp _ -> PermType
    (* Struct types *)
    | New (id, _) ->
        StructType id
    | Dot (_, id, _) ->
        let decl = IdMap.find id cu.var_decls in
        (match decl.v_type with
        | MapType (_, ty) -> ty
        | _ -> AnyType)
    (* Other stuff *)
    | Null (ty, _) -> ty
    | ProcCall (id, _, _) ->
        let decl = IdMap.find id cu.proc_decls in
        (match decl.p_returns with
        | [rid] -> 
            let rdecl = IdMap.find rid decl.p_locals in
            rdecl.v_type
        | _ -> AnyType)
    | PredApp (id, _, _) ->
        let decl = IdMap.find id cu.pred_decls in
        (match decl.pr_outputs with
        | [] -> BoolType
        | [rid] -> 
            let rdecl = IdMap.find rid decl.pr_locals in
            rdecl.v_type
        | _ -> AnyType)
    | Ident (id, _) ->
        let decl = 
          try
            IdMap.find id locals
          with Not_found ->
            IdMap.find id cu.var_decls
        in
        decl.v_type
    | Annot (e, _, _) ->
        te e
    | UnaryOp _
    | BinaryOp _ -> failwith "impossible"
  in 
  te e
    
let infer_types cu locals ty e =
  let rec it locals ty = function
    (* Non-ambiguous Boolean operators *)
    | UnaryOp (OpNot, e, pos) ->
        UnaryOp (OpNot, it locals BoolType e, pos)
    | BinaryOp (e1, OpImpl, e2, _, pos) ->
        let ty, e1, e2 = itp locals BoolType e1 e2 in
        ignore (match_types pos ty BoolType);
        BinaryOp (e1, OpImpl, e2, BoolType, pos)
    (* Ambiguous relational operators *)
    | BinaryOp (e1, (OpEq as op), e2, _, pos)
    | BinaryOp (e1, (OpGt as op), e2, _, pos)
    | BinaryOp (e1, (OpLt as op), e2, _, pos)
    | BinaryOp (e1, (OpGeq as op), e2, _, pos)
    | BinaryOp (e1, (OpLeq as op), e2, _, pos) ->
        let _, e1, e2 = itp locals AnyType e1 e2 in
        let ty = match_types pos ty BoolType in
        BinaryOp (e1, op, e2, ty, pos)
    (* Unary integer operators *)
    | UnaryOp (OpMinus, e, pos) ->
        let e1 = it locals IntType e in
        ignore (match_types pos ty IntType);
        UnaryOp (OpMinus, e1, pos)
    (* Binary integer operators *)
    | BinaryOp (e1, (OpMinus as op), e2, _, pos)
    | BinaryOp (e1, (OpPlus as op), e2, _, pos)
    | BinaryOp (e1, (OpMult as op), e2, _, pos)
    | BinaryOp (e1, (OpDiv as op), e2, _, pos)
    (* Ambiguous binary Boolean operatators *)
    | BinaryOp (e1, (OpAnd as op), e2, _, pos)
    | BinaryOp (e1, (OpOr as op), e2, _, pos)
    (* Binary set operators *)
    | BinaryOp (e1, (OpDiff as op), e2, _, pos)
    | BinaryOp (e1, (OpUn as op), e2, _, pos)
    | BinaryOp (e1, (OpInt as op), e2, _, pos) ->
        let ty, e1, e2 = itp locals ty e1 e2 in
        BinaryOp (e1, op, e2, ty, pos)
    | BinaryOp (e1, OpIn, e2, _, pos) ->
        let e1 = it locals AnyType e1 in
        let ety = type_of_expr cu locals e1 in
        let e2 = it locals (SetType ety) e2 in
        let ety1 = match type_of_expr cu locals e2 with
        | SetType ety1 -> ety1
        | _ -> failwith "impossible"
        in
        let e1 =
          if ety1 <> ety then it locals ety1 e1 else e1
        in
        ignore (match_types pos ty BoolType);
        BinaryOp (e1, OpIn, e2, BoolType, pos)
    (* Integer constants *)
    | IntVal (_, pos) as e ->
        ignore (match_types pos ty IntType);
        e
    (* Boolean constants *)
    | BoolVal (_, pos) as e ->
        ignore (match_types pos ty BoolType);
        e
    (* Permissions *)
    | Emp pos as e ->
        ignore (match_types pos ty PermType);
        e
    | Access (e, pos) ->
        let e = it locals (SetType AnyRefType) e in
        ignore (match_types pos ty PermType);
        Access (e, pos)
    | BinaryOp (e1, (OpSepStar as op), e2, _, pos)
    | BinaryOp (e1, (OpSepPlus as op), e2, _, pos)
    | BinaryOp (e1, (OpSepIncl as op), e2, _, pos) ->
        let ty, e1, e2 = itp locals PermType e1 e2 in
        ignore (match_types pos ty PermType);
        BinaryOp (e1, op, e2, PermType, pos)
    | BinaryOp (e1, OpPts, e2, _, pos) ->
        let _, e1, e2 = itp locals AnyType e1 e2 in
        ignore (match_types pos ty PermType);
        BinaryOp (e1, OpPts, e2, PermType, pos)
    (* Set enumerations *)
    | Setenum (ety, es, pos) ->
        let ety1, es1 =
          List.fold_right (fun e (ety, es) ->
            let e = it locals ety e in
            type_of_expr cu locals e, e :: es)
            es (ety, [])
        in
        let es1 =
          if ety <> ety1
          then List.map (it locals ety1) es1
          else es1
        in
        ignore (match_types pos ty (SetType ety));
        Setenum (ety1, es1, pos)
    | GuardedQuant (b, id, e, f, pos) ->
        let e1 = it locals (SetType AnyType) e in
        let ety = type_of_expr cu locals e1 in
        let idty = match ety with
        | SetType ty -> ty
        | _ -> type_error pos (SetType AnyType) ety
        in
        let decl = var_decl id idty false false pos pos in
        let locals1 = IdMap.add id decl locals in
        let f1 = it locals1 ty f in
        GuardedQuant (b, id, e1, f1, pos)
    | Quant (b, decls, f, pos) ->
        let locals1 =
          List.fold_right
            (fun decl locals1 -> IdMap.add decl.v_name decl locals1)
            decls locals
        in
        let f1 = it locals1 ty f in
        Quant (b, decls, f1, pos)
    (* Reference types *)
    | New (id, pos) as e->
        ignore (match_types pos ty (StructType id));
        e
    | Dot (e, id, pos) ->
        let decl = IdMap.find id cu.var_decls in
        let rty, dty =
          match decl.v_type with
          | MapType (rty, dty) ->
              rty, dty
          | fty -> type_error pos (MapType (AnyRefType, AnyType)) fty
        in
        let e1 = it locals dty e in
        ignore (match_types pos ty rty);
        Dot (e1, id, pos)
    | Null (nty, pos) -> Null (match_types pos ty nty, pos)
    (* Other stuff *)
    | BtwnPred (e1, e2, e3, e4, pos) ->
        let e1 = it locals (MapType (AnyRefType, AnyRefType)) e1 in
        let fty = type_of_expr cu locals e1 in
        let id = match fty with
        | MapType (StructType id1, StructType id2) ->
            if id1 <> id2
            then type_error pos (MapType (StructType id1, StructType id1)) fty
            else id1
        | _ -> failwith "impossible"
        in
        let e2 = it locals (StructType id) e2 in
        let e3 = it locals (StructType id) e3 in
        let e4 = it locals (StructType id) e4 in
        BtwnPred (e1, e2, e3, e4, pos)
    | ProcCall (id, es, pos) ->
        let decl = IdMap.find id cu.proc_decls in
        let ftys =
          List.map (fun fid ->
            let vdecl = IdMap.find fid decl.p_locals in
            vdecl.v_type)
            decl.p_formals
        in
        let es1 = List.map2 (it locals) ftys es in
        (match decl.p_returns with
        | [rid] -> 
            let rdecl = IdMap.find rid decl.p_locals in
            ignore (match_types pos ty rdecl.v_type)
        | _ -> ());
        ProcCall (id, es1, pos)
    | PredApp (id, es, pos) ->
        let decl = IdMap.find id cu.pred_decls in
        let ftys =
          List.map
            (fun fid -> (IdMap.find fid decl.pr_locals).v_type)
            (decl.pr_formals @ decl.pr_footprints)
        in
        let es1, ftys, es =
          Util.map2_remainder (it locals) ftys es
        in
        (* Check whether number of actual arguments is correct *)
        let _ = 
          match ty, ftys, es with
          | _, _, _ :: _
          | BoolType, _ :: _, _ ->
              pred_arg_mismatch_error pos (fst id) (List.length ftys)
          | PermType, _ :: _, _ ->
              if List.length es1 <> List.length decl.pr_formals then
                pred_arg_mismatch_error pos (fst id) (List.length decl.pr_formals)
          | _ -> ()
        in
        (* Check whether return type matches expected type *)
        let _ =
          match decl.pr_outputs with
          | [rid] -> 
            let rdecl = IdMap.find rid decl.pr_locals in
            ignore (match_types pos ty rdecl.v_type)
          | _ -> ()
        in
        PredApp (id, es1, pos)
    | Ident (id, pos) as e ->
        let decl = 
          try
            IdMap.find id locals
          with Not_found ->
            IdMap.find id cu.var_decls
        in
        let _ = match_types pos ty decl.v_type in
        e
    | Annot (e, a, pos) ->
        (* TODO: check annotation *)
        Annot (it locals ty e, a, pos)
    | UnaryOp _
    | BinaryOp _ -> failwith "impossible"
  and itp locals ty e1 e2 =
    let e1 = it locals ty e1 in
    let ty1 = type_of_expr cu locals e1 in
    let e2 = it locals ty1 e2 in
    let ty2 = type_of_expr cu locals e2 in
    let e1 =
      if ty1 <> ty2
      then it locals ty2 e1
      else e1
    in
    ty2, e1, e2
  in it locals ty e

(** Returns true iff [ty1] is a subtype of [ty2]. *)
let rec is_sub_type ty1 ty2 = 
  match ty1, ty2 with
  | AnyRefType, StructType _
  | StructType _, AnyRefType
  | _, AnyType -> true
  | SetType ty1, SetType ty2 ->
      is_sub_type ty1 ty2
  | MapType (dty1, rty1), MapType (dty2, rty2) ->
      is_sub_type dty2 dty1 && is_sub_type rty1 rty2
  | _ -> ty1 = ty2

