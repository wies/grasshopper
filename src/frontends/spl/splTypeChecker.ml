open Util
open Grass
open SplSyntax
open SplErrors
  
let match_types pos oty1 oty2 =
  let rec mt ty1 ty2 =
    match ty1, ty2 with
    | PermType, BoolType -> BoolType
    | AnyRefType, StructType _
    | AnyRefType, ArrayType _
    | AnyRefType, ArrayCellType _ -> ty2
    | StructType _, AnyRefType
    | ArrayType _, AnyRefType
    | ArrayCellType _, AnyRefType -> ty1
    | AnyType, _ -> ty2
    | _, AnyType -> ty1
    | MapType (IntType, ty1), ArrayType ty2
    | MapType (AnyType, ty1), ArrayType ty2 
    | ArrayType ty1, ArrayType ty2 ->
        ArrayType (mt ty1 ty2)
    | ArrayCellType ty1, ArrayCellType ty2 ->
        ArrayCellType (mt ty1 ty2)
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
    | PermType, BoolType
    | BoolType, PermType -> PermType
    | AnyRefType, StructType _
    | AnyRefType, ArrayType _
    | AnyRefType, ArrayCellType _ -> ty2
    | StructType _, AnyRefType
    | ArrayType _, AnyRefType
    | ArrayCellType _, AnyRefType -> ty1
    | AnyType, _ -> ty2
    | _, AnyType -> ty1
    | MapType (IntType, ty1), ArrayType ty2 
    | ArrayType ty1, MapType (IntType, ty2) 
    | MapType (AnyType, ty1), ArrayType ty2 
    | ArrayType ty1, MapType (AnyType, ty2) 
    | ArrayType ty1, ArrayType ty2 ->
        ArrayType (mt ty1 ty2)
    | ArrayCellType ty1, ArrayCellType ty2 ->
        ArrayCellType (mt ty1 ty2)
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
    | BinaryOp (_, OpEq, _, _, _)
    | BinaryOp (_, OpGt, _, _, _)
    | BinaryOp (_, OpLt, _, _, _)
    | BinaryOp (_, OpGeq, _, _, _)
    | BinaryOp (_, OpLeq, _, _, _)
    | BinaryOp (_, OpIn, _, _, _)
    | PredApp (BtwnPred, _, _)
    | PredApp (ReachPred, _, _)
    | PredApp (FramePred, _, _)
    | PredApp (DisjointPred, _, _)
    | BoolVal _ -> BoolType
    (* Int return values *)
    | UnaryOp (OpToInt, _, _)
    | IntVal _ -> IntType
    (* Byte values *)
    | UnaryOp (OpToByte, _, _) -> ByteType
    (* Int or Byte return values *)
    | UnaryOp (OpUMinus, e, _)
    | UnaryOp (OpUPlus, e, _) 
    | BinaryOp (e, (OpMinus | OpPlus | OpMult | OpDiv | OpMod), _, _, _)
    | UnaryOp (OpBvNot, e, _)
    | BinaryOp (e, OpBvAnd, _, _, _)
    | BinaryOp (e, OpBvOr, _, _, _)
    | BinaryOp (e, OpBvShiftL, _, _, _)
    | BinaryOp (e, OpBvShiftR, _, _, _) ->
        te e
    (* Set return values *)
    | BinaryOp (e, OpDiff, _, _, _)
    | BinaryOp (e, OpUn, _, _, _)
    | BinaryOp (e, OpInt, _, _, _) ->
        te e
    | Binder (SetComp, [v], _, _) ->
        (match v with
        | GuardedVar (_, e) -> SetType (te e)
        | UnguardedVar v -> SetType (v.v_type))
    | Binder (SetComp, _, _, _) -> failwith "invalid set comprehension"        
    | Setenum (ty, _, _) ->
        SetType ty
    (* Permission types *)
    | BinaryOp (_, OpSepStar, _, _, _)
    | BinaryOp (_, OpSepPlus, _, _, _)
    | BinaryOp (_, OpPts, _, _, _)
    | BinaryOp (_, OpSepIncl, _, _, _)
    | PredApp (AccessPred, _, _)
    | Dirty _
    | Emp _ -> PermType
    (* Permission or Bool types *)
    | Binder ((Forall | Exists), _, f, _) ->
        te f
    | BinaryOp (e1, (OpAnd | OpOr | OpImpl), e2, ty, pos) ->
        ty
    (* Struct and array types *)
    | New (ty, _, _) ->
        ty
    | Read (map, _, _) ->
        (match te map with
        | MapType (_, ty) -> ty
        | ArrayType ty -> ty
        | _ -> AnyType)
    | Write (map, _, _, _) -> te map
    | ConstrApp (id, _, _) | DestrApp (id, _, _) ->
        let decl = IdMap.find id cu.fun_decls in
        decl.f_res
    | UnaryOp ((OpOld | OpKnown), e, _) -> te e        
    | UnaryOp (OpLength, map, _) -> IntType
    | UnaryOp (OpArrayOfCell, c, _) ->
        (match te c with
        | ArrayCellType srt -> ArrayType srt
        | _ -> AnyType)
    | UnaryOp (OpIndexOfCell, c, _) -> IntType
    | UnaryOp (OpArrayCells, map, _) ->
        (match te map with
        | ArrayType srt -> MapType (IntType, ArrayCellType srt)
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
    | PredApp (Pred id, _, _) ->
        let decl = IdMap.find id cu.pred_decls in
        (match decl.pr_outputs with
        | [] -> decl.pr_body |> Opt.map te |> Opt.get_or_else BoolType
        | [rid] -> 
            let rdecl = IdMap.find rid decl.pr_locals in
            rdecl.v_type
        | _ -> AnyType)
    | Ident (id, _) ->
        (try
          (IdMap.find id locals).v_type
        with Not_found ->
          try (IdMap.find id cu.var_decls).v_type
          with Not_found -> AnyType)
    | Annot (e, _, _) ->
        te e
  in 
  te e

(** Infer the types in expression [e] and check whether its type is compatible with [ty].
 ** The typing environment is given by the parameters [cu] and [locals]. *)    
let infer_types cu locals ty e =
  let elem_type_of = function
    | SetType ty -> ty
    | _ -> failwith "impossible"
  in
  let rec it locals ty = function
    (* Non-ambiguous Boolean operators *)
    | UnaryOp (OpNot as op, e, pos) ->
        let e1, ty = it locals ty e in
        UnaryOp (op, e1, pos), ty
    | BinaryOp (e1, OpImpl, e2, _, pos) ->
        let e1, _ = it locals BoolType e1 in
        let e2, ty1 = it locals ty e2 in
        BinaryOp (e1, OpImpl, e2, ty1, pos), ty1
    (* Non-ambiguous Int/Byte operators*)
    | UnaryOp (OpToByte, e, pos) ->
        let e1, ty = it locals IntType e in
        ignore (match_types pos ty IntType);
        UnaryOp (OpToByte, e1, pos), ByteType
    | UnaryOp (OpToInt, e, pos) ->
        let e1, ty = it locals ByteType e in
        ignore (match_types pos ty ByteType);
        UnaryOp (OpToInt, e1, pos), IntType
    (* Ambiguous relational operators *)
    | BinaryOp (e1, (OpEq as op), e2, _, pos) ->
        let e1, e2, ty1 = itp locals AnyType e1 e2 in
        BinaryOp (e1, op, e2, BoolType, pos), match_types pos ty BoolType
    | BinaryOp (e1, (OpGt as op), e2, _, pos)
    | BinaryOp (e1, (OpLt as op), e2, _, pos)
    | BinaryOp (e1, (OpGeq as op), e2, _, pos)
    | BinaryOp (e1, (OpLeq as op), e2, _, pos) ->
        let e1, e2, ty1 = itp locals AnyType e1 e2 in
        if ty1 <> IntType && ty1 <> ByteType then
          ignore (match_types (pos_of_expr e1) ty1 (SetType AnyType));
        BinaryOp (e1, op, e2, BoolType, pos), match_types pos ty BoolType
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
        let ty11 = elem_type_of ty2 in
        let e1 =
          if ty1 <> ty11 then fst (it locals ty11 e1) else e1
        in
        BinaryOp (e1, OpIn, e2, BoolType, pos), match_types pos ty BoolType
    (* Ambiguous Int/Byte operators*)
    | UnaryOp (OpUMinus as op, e, pos) 
    | UnaryOp (OpUPlus as op, e, pos) 
    | UnaryOp (OpBvNot as op, e, pos) ->
      let e1, ty = it locals AnyType e in
      if ty = IntType || ty = ByteType then
        UnaryOp (op, e1, pos), ty
      else
        type_error pos IntType ty
    | BinaryOp (e1, ((OpMinus | OpPlus | OpMult | OpDiv | OpMod) as op), e2, _, pos)
    | BinaryOp (e1, ((OpBvAnd | OpBvOr)  as op), e2, _, pos) ->
      let e1, e2, ty = itp locals ty e1 e2 in
      if ty = IntType || ty = ByteType then
        BinaryOp (e1, op, e2, ty, pos), ty
      else
        type_error pos IntType ty
    | BinaryOp (e1, (OpBvShiftL as op), e2, _, pos)
    | BinaryOp (e1, (OpBvShiftR as op), e2, _, pos) ->
      let e1, ty1 = it locals AnyType e1 in
      let e2, ty2 = it locals IntType e2 in
      if ty1 = IntType || ty1 = ByteType then
        BinaryOp (e1, op, e2, ty1, pos), ty1
      else
        type_error pos IntType ty
    (* Integer constants *)
    | IntVal (_, pos) as e ->
        e, match_types pos ty IntType
    (* Boolean constants *)
    | BoolVal (_, pos) as e ->
        e, match_types pos ty BoolType
    (* Permissions *)
    | Emp pos as e ->
        e, match_types pos ty PermType
    | PredApp (AccessPred, es, pos) ->
        (match es with
        | [e] ->
            let e, _ = it locals (SetType AnyRefType) e in
            PredApp (AccessPred, [e], pos), match_types pos ty PermType
        | _ -> pred_arg_mismatch_error pos ("acc", 0) 1)
    | Dirty (e, es, pos) ->
        let e, _ = it locals PermType e in
        let es = List.map (it locals AnyType >> fst) es in
        Dirty (e, es, pos), match_types pos ty PermType
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
        let ety1 = match_types pos ty (SetType ety) in
        let es1, ety2 =
          List.fold_right (fun e (es, ety) ->
            let e, ety1 = it locals ety e in
            e :: es, ety1)
            es ([], elem_type_of ety1)
        in
        let es1 =
          if ety1 <> ety2
          then List.map (fun e -> fst (it locals ety2 e)) es1
          else es1
        in
        Setenum (ety2, es1, pos), SetType ety2
    (* Binders *)
    | Binder (b, decls, f, pos) ->
        let decls1, (locals1, vty_opt) =
          Util.fold_left_map
            (fun (locals, vty_opt) decl ->
              match decl with
              | GuardedVar (id, e) ->
                  let e1, ety = it locals (SetType AnyType) e in
                  let idty = match ety with
                  | SetType ty -> ty
                  | _ -> type_error pos (SetType AnyType) ety
                  in
                  let decl = var_decl id idty false false pos pos in
                  GuardedVar (id, e1),
                  (IdMap.add id decl locals, Opt.or_else ety vty_opt)
              | UnguardedVar v ->
                  UnguardedVar v,
                  (IdMap.add v.v_name v locals, Opt.or_else v.v_type vty_opt)
            )
            (locals, None)
            decls
        in
        let f1, ty =
          match b with
          | Exists | Forall ->
              it locals1 ty f
          | SetComp ->
              fst (it locals1 BoolType f),
              match_types pos ty (SetType (Opt.get vty_opt))
        in
        Binder (b, decls1, f1, pos), ty
    (* Reference and array types *)
    | New (nty, es, pos) ->
        let es1 =
          match nty, es with
          | StructType _, _ :: _ -> 
              alloc_arg_mismatch_error pos 0
          | ArrayType _, []
          | ArrayType _, _ :: _ :: _ ->
              alloc_arg_mismatch_error pos 1
          | StructType _, es
          | ArrayType _, es ->
              List.map (fun e -> fst (it locals IntType e)) es
          | nty, _ ->
              alloc_type_error pos nty
        in
        let ty1 = match_types pos ty nty in
        New (ty1, es1, pos), ty1
    | UnaryOp ((OpOld | OpKnown as op), e, pos) ->
        let e1, ty1 = it locals ty e in
        UnaryOp(op, e1, pos), ty1
    | UnaryOp (OpLength, map, pos) ->
        let map1, _ = it locals (ArrayType AnyType) map in
        UnaryOp (OpLength, map1, pos), match_types pos ty IntType
    | UnaryOp (OpArrayOfCell, c, pos) ->
        let ety =
          match ty with
          | ArrayType ety -> ety
          | _ -> AnyType
        in
        let c1, cty = it locals (ArrayCellType ety) c in
        let ety =
          match cty with
          | ArrayCellType ety -> ety
          | _ -> ety
        in
        UnaryOp (OpArrayOfCell, c1, pos), match_types pos ty (ArrayType ety)
    | UnaryOp (OpIndexOfCell, c, pos) ->
        let c1, _ = it locals (ArrayCellType AnyType) c in
        UnaryOp (OpIndexOfCell, c1, pos), match_types pos ty IntType
    | UnaryOp (OpArrayCells, map, pos) ->
        let ety =
          match ty with
          | ArrayCellType ety -> ety
          | _ -> AnyType
        in
        let map1, mty = it locals (ArrayType ety) map in
        let ety =
          match mty with
          | ArrayType ety -> ety
          | _ -> ety
        in
        UnaryOp (OpArrayCells, map1, pos), match_types pos ty (MapType (IntType, ArrayCellType ety))
     (*| Dot (e, id, pos) ->
        let decl = IdMap.find id cu.var_decls in
        let dty, rty =
          match decl.v_type with
          | MapType (dty, rty) ->
              dty, rty
          | fty -> type_error pos (MapType (AnyRefType, AnyType)) fty
        in
        let e1, _ = it locals dty e in
       Dot (e1, id, pos), match_types pos ty rty*)
    | Read (map, idx, pos) ->
        let map1, mty = it locals (MapType (AnyType, ty)) map in
        let dty, rty = match mty with
        | MapType (dty, rty) -> dty, rty
        | ArrayType rty -> IntType, rty
        | _ -> failwith "impossible"
        in
        let idx1, dty = it locals dty idx in
        let map2, mty = it locals (MapType (dty, rty)) map1 in
        Read (map2, idx1, pos), rty
    | Write (map, idx, upd, pos) ->
        let map1, mty = it locals ty map in
        let dty, rty = match mty with
        | MapType (dty, rty) -> dty, rty
        | ArrayType rty -> IntType, rty
        | _ -> failwith "impossible"
        in
        let idx1, dty = it locals dty idx in
        let upd1, rty = it locals rty upd in
        let map2, mty = it locals (MapType (dty, rty)) map1 in
        Write (map2, idx1, upd1, pos), mty
    | ConstrApp (id, args, pos) ->
        let decl = IdMap.find id cu.fun_decls in
        let ty = match_types pos ty decl.f_res in
        let atys = decl.f_args in
        let args1 =
          try
            List.map2 (fun ty e -> fst (it locals ty e)) atys args
          with Invalid_argument _ ->
            constr_arg_mismatch_error pos id atys
        in
        ConstrApp (id, args1, pos), ty
    | DestrApp (id, arg, pos) ->
        let decl = IdMap.find id cu.fun_decls in
        let ty = match_types pos ty decl.f_res in
        let atys = decl.f_args in
        let args1 =
          try
            List.map2 (fun ty e -> fst (it locals ty e)) atys [arg]
          with Invalid_argument _ ->
            destr_arg_mismatch_error pos id atys
        in
        ConstrApp (id, args1, pos), ty
    | Null (nty, pos) ->
        let ty = match_types pos ty nty in
        Null (ty, pos), ty
    (* Other stuff *)
    | PredApp (BtwnPred as sym, es, pos)
    | PredApp (ReachPred as sym, es, pos) ->
        let arg_error () = 
          match sym with
          | BtwnPred -> pred_arg_mismatch_error pos ("Btwn", 0) 4
          | ReachPred -> pred_arg_mismatch_error pos ("Reach", 0) 3
          | _ -> failwith "impossible"
        in
        (match es with
        | e1 :: e2 :: e3 :: es1 ->
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
            ignore (match_types pos ty BoolType);
            (match sym, es1 with
            | BtwnPred, [e4] ->
                let e4, _ = it locals (StructType id) e4 in
                PredApp (BtwnPred, [e1; e2; e3; e4], pos), BoolType
            | ReachPred, [] ->
                PredApp (ReachPred, [e1; e2; e3], pos), BoolType
            | _ -> arg_error ())
        | _ -> arg_error ())   
    | PredApp (FramePred, es, pos) ->
        (match es with
        | [e1; e2; e3; e4] ->
            let e1, set_ty = it locals (SetType AnyRefType) e1 in
            let e2, _ = it locals set_ty e2 in
            let elem_ty = elem_type_of set_ty in
            let e3, fld_ty = it locals (MapType (elem_ty, AnyType)) e3 in
            let e4, fld_ty = it locals fld_ty e4 in
            PredApp (FramePred, [e1; e2; e3; e4], pos), match_types pos ty BoolType
        | _ -> pred_arg_mismatch_error pos ("Frame", 0) 4)
    | PredApp (DisjointPred, es, pos) ->
      (match es with
        [e1; e2] ->
          let e1, set_ty = it locals (SetType AnyRefType) e1 in
          let e2, _ = it locals set_ty e2 in
          PredApp (DisjointPred, [e1; e2], pos), match_types pos ty BoolType
      | _ -> pred_arg_mismatch_error pos ("Disjoint", 0) 2)
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
    | PredApp (Pred id, es, pos) ->
        let decl = IdMap.find id cu.pred_decls in
        let ftys =
          List.map
            (fun fid -> (IdMap.find fid decl.pr_locals).v_type)
            decl.pr_formals
        in
        let es1, rftys, res =
          Util.map2_remainder (fun ty e -> fst (it locals ty e)) ftys es
        in
        let arg_error num_args =
          match ty with
          | PermType | BoolType ->
              pred_arg_mismatch_error pos id num_args
          | _ ->
              fun_arg_mismatch_error pos id num_args
        in
        (* Check whether number of actual arguments is correct *)
        let _ = 
          match ty, rftys, res with
          | PermType, _ :: _, [] ->
              if List.length es1 <> List.length decl.pr_formals then
                arg_error (List.length decl.pr_formals)
          | _, _ :: _, _ | _, _, _ :: _ ->
              arg_error (List.length ftys)
          | _ -> ()
        in
        (* Check whether return type matches expected type *)
        let rty =
          match decl.pr_outputs with
          | [rid] -> 
              let rdecl = IdMap.find rid decl.pr_locals in
              match_types pos ty rdecl.v_type
          | _ ->
              let body_ty =
                decl.pr_body |>
                Opt.map (type_of_expr cu locals) |>
                Opt.get_or_else BoolType
              in
              match_types pos ty body_ty
        in
        PredApp (Pred id, es1, pos), rty
    | Ident (id, pos) as e ->
        let decl = 
          try
            IdMap.find id locals
          with Not_found ->
            try IdMap.find id cu.var_decls
            with Not_found ->
              unknown_ident_error id pos
        in
        e, match_types pos ty decl.v_type
    | Annot (e, a, pos) ->
        let e1, ty = it locals ty e in
        let a1 =
          match a with
          | GeneratorAnnot (es, ge) ->
              let es1 = List.map (fun (e, ids) -> (fst (it locals AnyType e), ids)) es in
              let ge1, _ = it locals AnyType ge in
              GeneratorAnnot (es1, ge1)
          | PatternAnnot p ->
              let p1, _ = it locals AnyType p in
              PatternAnnot p1
          | _ -> a
        in
        Annot (e1, a1, pos), ty
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
  | SetType ty
  | ArrayType ty
  | ArrayCellType ty ->
      is_abstract_type ty
  | MapType (dty, rty) ->
      is_abstract_type dty ||
      is_abstract_type rty
  | _ -> false

    
