open Grass
open SplSyntax

let pred_arg_mismatch_error pos id expected =
  ProgError.error pos (Printf.sprintf "Predicate %s expects %d argument(s)" (GrassUtil.name id) expected)

let proc_arg_mismatch_error pos id expected =
  ProgError.error pos 
    (Printf.sprintf "Procedure %s expects %d argument(s)" 
       (GrassUtil.name id) (List.length expected))

let type_error pos exp_ty fnd_ty =
  let ty_str ty = "expression of type " ^ string_of_type ty in
  ProgError.type_error pos
    ("Expected an " ^ ty_str exp_ty ^ " but found an " ^ ty_str fnd_ty)

let match_types pos oty1 oty2 =
  let rec mt ty1 ty2 =
    match ty1, ty2 with
    | PermType, BoolType -> PermType
    | AnyRefType, StructType _ -> ty2
    | StructType _, AnyRefType -> ty1
    | AnyType, _ -> ty2
    | _, AnyType -> ty1
    | ArrayType ty1, ArrayType ty2 ->
        ArrayType (mt ty1 ty2)
    | SetType ty1, SetType ty2 ->
        SetType (mt ty1 ty2)
    | MapType (dty1, rty1), MapType (dty2, rty2) ->
        let dty = mt dty1 dty2 in
        let rty = mt rty1 rty2 in
        MapType (dty, rty)
    | ty, tty when ty = tty -> ty2
    | _ -> type_error pos oty1 oty2
  in mt oty1 oty2

let merge_types pos oty1 oty2 =
  let rec mt ty1 ty2 =
    match ty1, ty2 with
    | PermType, BoolType -> PermType
    | BoolType, PermType -> PermType
    | AnyRefType, StructType _ -> ty2
    | StructType _, AnyRefType -> ty1
    | AnyType, _ -> ty2
    | _, AnyType -> ty1
    | ArrayType ty1, ArrayType ty2 ->
        ArrayType (mt ty1 ty2)
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
    (* Array types *)
    | ArrayAccess (ar, _, _) ->
        (match te ar with
        | ArrayType ty -> ty
        | _ -> AnyType)
    (* Other stuff *)
    | Null (ty, _) -> ty
    | ProcCall (id, _, _) ->
        let decl = IdMap.find id cu.proc_decls in
        (match decl.p_returns with
        | [rid] -> 
            let rdecl = IdMap.find rid decl.p_locals in
            rdecl.v_type
        | _ -> UnitType)
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

(** Infer the types in expression [e] and check whether its type is compatible with [ty].
 ** The typing environment is given by the parameters [cu] and [locals]. *)    
let infer_types cu locals ty e =
  let rec it locals ty = function
    (* Non-ambiguous Boolean operators *)
    | UnaryOp (OpNot, e, pos) ->
        let e1, ty = it locals ty e in
        UnaryOp (OpNot, e1, pos), ty
    | BinaryOp (e1, OpImpl, e2, _, pos) ->
        let e1, e2, ty = itp locals BoolType e1 e2 in
        BinaryOp (e1, OpImpl, e2, ty, pos), ty
    (* Ambiguous relational operators *)
    | BinaryOp (e1, (OpEq as op), e2, _, pos)
    | BinaryOp (e1, (OpGt as op), e2, _, pos)
    | BinaryOp (e1, (OpLt as op), e2, _, pos)
    | BinaryOp (e1, (OpGeq as op), e2, _, pos)
    | BinaryOp (e1, (OpLeq as op), e2, _, pos) ->
        let e1, e2, _ = itp locals AnyType e1 e2 in
        ignore (match_types pos ty BoolType);
        BinaryOp (e1, op, e2, BoolType, pos), BoolType
    (* Unary integer operators *)
    | UnaryOp (OpMinus, e, pos) ->
        let e1, _ = it locals IntType e in
        ignore (match_types pos ty IntType);
        UnaryOp (OpMinus, e1, pos), IntType
    (* Binary integer operators *)
    | BinaryOp (e1, (OpMinus as op), e2, _, pos)
    | BinaryOp (e1, (OpPlus as op), e2, _, pos)
    | BinaryOp (e1, (OpMult as op), e2, _, pos)
    | BinaryOp (e1, (OpDiv as op), e2, _, pos)
    (* Ambiguous binary Boolean operators *)
    | BinaryOp (e1, (OpAnd as op), e2, _, pos)
    | BinaryOp (e1, (OpOr as op), e2, _, pos)
    (* Binary set operators *)
    | BinaryOp (e1, (OpDiff as op), e2, _, pos)
    | BinaryOp (e1, (OpUn as op), e2, _, pos)
    | BinaryOp (e1, (OpInt as op), e2, _, pos) ->
        let e1, e2, ty = itp locals ty e1 e2 in
        BinaryOp (e1, op, e2, ty, pos), ty
    | BinaryOp (e1, OpIn, e2, _, pos) ->
        let e1, ty1 = it locals AnyType e1 in
        let e2, ty2 = it locals (SetType ty1) e2 in
        let ty11 = match ty2 with
        | SetType ty11 -> ty11
        | _ -> failwith "impossible"
        in
        let e1 =
          if ty1 <> ty11 then fst (it locals ty11 e1) else e1
        in
        ignore (match_types pos ty BoolType);
        BinaryOp (e1, OpIn, e2, BoolType, pos), BoolType
    (* Integer constants *)
    | IntVal (_, pos) as e ->
        e, match_types pos ty IntType
    (* Boolean constants *)
    | BoolVal (_, pos) as e ->
        ignore (match_types pos ty BoolType);
        e, BoolType
    (* Permissions *)
    | Emp pos as e ->
        e, match_types pos ty PermType
    | Access (e, pos) ->
        let e, _ = it locals (SetType AnyRefType) e in
        Access (e, pos), match_types pos ty PermType
    | BinaryOp (e1, (OpSepStar as op), e2, _, pos)
    | BinaryOp (e1, (OpSepPlus as op), e2, _, pos)
    | BinaryOp (e1, (OpSepIncl as op), e2, _, pos) ->
        let e1, e2, _ = itp locals (match_types pos ty PermType) e1 e2 in
        BinaryOp (e1, op, e2, PermType, pos), PermType
    | BinaryOp (e1, OpPts, e2, _, pos) ->
        let e1, e2, _ = itp locals AnyType e1 e2 in
        let ty = match_types pos ty PermType in
        BinaryOp (e1, OpPts, e2, ty, pos), ty
    (* Set enumerations *)
    | Setenum (ety, es, pos) ->
        let es1, ety1 =
          List.fold_right (fun e (es, ety) ->
            let e, ety1 = it locals ety e in
            e :: es, ety1)
            es ([], ety)
        in
        let es1 =
          if ety <> ety1
          then List.map (fun e -> fst (it locals ety1 e)) es1
          else es1
        in
        Setenum (ety1, es1, pos), match_types pos ty (SetType ety)
    | GuardedQuant (b, id, e, f, pos) ->
        let e1, ety = it locals (SetType AnyType) e in
        let idty = match ety with
        | SetType ty -> ty
        | _ -> type_error pos (SetType AnyType) ety
        in
        let decl = var_decl id idty false false pos pos in
        let locals1 = IdMap.add id decl locals in
        let f1, ty = it locals1 (match_types pos ty BoolType) f in
        GuardedQuant (b, id, e1, f1, pos), ty
    | Quant (b, decls, f, pos) ->
        let locals1 =
          List.fold_right
            (fun decl locals1 -> IdMap.add decl.v_name decl locals1)
            decls locals
        in
        let f1, ty = it locals1 (match_types pos ty BoolType) f in
        Quant (b, decls, f1, pos), ty
    (* Reference types *)
    | New (id, pos) as e ->
        e, match_types pos ty (StructType id)
    | Dot (e, id, pos) ->
        let decl = IdMap.find id cu.var_decls in
        let dty, rty =
          match decl.v_type with
          | MapType (dty, rty) ->
              dty, rty
          | fty -> type_error pos (MapType (AnyRefType, AnyType)) fty
        in
        let e1, _ = it locals dty e in
        Dot (e1, id, pos), match_types pos ty rty
    | Null (nty, pos) ->
        let ty = match_types pos ty nty in
        Null (ty, pos), ty
    (* Array types *)
    | ArrayAccess (ar, idx, pos) ->
        let ar1, ty = it locals (ArrayType ty) ar in
        let idx1, _ = it locals IntType idx in
        ArrayAccess (ar1, idx1, pos), ty
    (* Other stuff *)
    | BtwnPred (e1, e2, e3, e4, pos) ->
        let e1, fty = it locals (MapType (AnyRefType, AnyRefType)) e1 in
        let id = match fty with
        | MapType (StructType id1, StructType id2) ->
            if id1 <> id2
            then type_error pos (MapType (StructType id1, StructType id1)) fty
            else id1
        | _ -> failwith "impossible"
        in
        let e2, _ = it locals (StructType id) e2 in
        let e3, _ = it locals (StructType id) e3 in
        let e4, _ = it locals (StructType id) e4 in
        BtwnPred (e1, e2, e3, e4, pos), match_types pos ty BoolType
    | ProcCall (id, es, pos) ->
        let decl = IdMap.find id cu.proc_decls in
        let formals = List.filter (fun p -> not (IdMap.find p decl.p_locals).v_implicit) decl.p_formals in
        let ftys =
          List.map (fun fid ->
            let vdecl = IdMap.find fid decl.p_locals in
            vdecl.v_type)
            formals
        in
        let es1 =
          try List.map2 (fun ty e -> fst (it locals ty e)) ftys es
          with Invalid_argument _ ->
            proc_arg_mismatch_error pos id ftys
        in
        let rty =
          match decl.p_returns with
          | [rid] -> 
              let rdecl = IdMap.find rid decl.p_locals in
              match_types pos ty rdecl.v_type
          | _ -> match_types pos ty UnitType
        in
        ProcCall (id, es1, pos), rty
    | PredApp (id, es, pos) ->
        let decl = IdMap.find id cu.pred_decls in
        let ftys =
          List.map
            (fun fid -> (IdMap.find fid decl.pr_locals).v_type)
            (decl.pr_formals @ decl.pr_footprints)
        in
        let es1, rftys, res =
          Util.map2_remainder (fun ty e -> fst (it locals ty e)) ftys es
        in
        (* Check whether number of actual arguments is correct *)
        let _ = 
          match ty, rftys, res with
          | _, _, _ :: _
          | BoolType, _ :: _, _ ->
              pred_arg_mismatch_error pos id (List.length ftys)
          | PermType, _ :: _, _ ->
              if List.length es1 <> List.length decl.pr_formals then
                pred_arg_mismatch_error pos id (List.length decl.pr_formals)
          | _ -> ()
        in
        (* Check whether return type matches expected type *)
        let rty =
          match decl.pr_outputs with
          | [rid] -> 
              let rdecl = IdMap.find rid decl.pr_locals in
              match_types pos ty rdecl.v_type
          | _ ->
              match_types pos ty BoolType
        in
        PredApp (id, es1, pos), rty
    | Ident (id, pos) as e ->
        let decl = 
          try
            IdMap.find id locals
          with Not_found ->
            IdMap.find id cu.var_decls
        in
        e, match_types pos ty decl.v_type
    | Annot (e, a, pos) ->
        (* TODO: check annotation *)
        let e1, ty = it locals ty e in
        Annot (e1, a, pos), ty
    | UnaryOp _
    | BinaryOp _ -> failwith "impossible"
  and itp locals ty e1 e2 =
    let e1, ty1 = it locals ty e1 in
    let e2, ty2 = it locals ty e2 in
    let ty = merge_types (pos_of_expr e2) ty1 ty2 in
    let e1 =
      if ty1 <> ty 
      then fst (it locals ty e1)
      else e1
    in
    let e2 =
      if ty2 <> ty
      then fst (it locals ty e2)
      else e2
    in
    e1, e2, ty
  in fst (it locals ty e)

let rec is_abstract_type = function
  | AnyRefType
  | AnyType -> true
  | SetType ty -> is_abstract_type ty
  | MapType (dty, rty) ->
      is_abstract_type dty ||
      is_abstract_type rty
  | _ -> false

    
