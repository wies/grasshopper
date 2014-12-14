open Grass
open SplSyntax

(** Computes SPL type of expression [e] in compilation unit [cu] and environment [locals].
  * Assumes that all identifiers in [e] have been resolved. *)
let type_of_expr cu locals e = 
  let rec te = function
    (* Bool return values *)
    | UnaryOp (OpNot, _, _)
    | BinaryOp (_, OpAnd, _, _)
    | BinaryOp (_, OpOr, _, _)
    | BinaryOp (_, OpImpl, _, _)
    | BinaryOp (_, OpEq, _, _)
    | BinaryOp (_, OpNeq, _, _)
    | BinaryOp (_, OpGt, _, _)
    | BinaryOp (_, OpLt, _, _)
    | BinaryOp (_, OpGeq, _, _)
    | BinaryOp (_, OpLeq, _, _)
    | BinaryOp (_, OpIn, _, _)
    | GuardedQuant _ 
    | Quant _
    | PredApp _ 
    | BoolVal _ -> BoolType
    (* Int return values *)
    | UnaryOp (OpMinus, _, _) 
    | BinaryOp (_, OpMinus, _, _)
    | BinaryOp (_, OpPlus, _, _)
    | BinaryOp (_, OpMult, _, _)
    | BinaryOp (_, OpDiv, _, _)
    | IntVal _ -> IntType
    (* Set return values *)
    | BinaryOp (e, OpDiff, _, _)
    | BinaryOp (e, OpUn, _, _)
    | BinaryOp (e, OpInt, _, _) ->
        te e
    | Setenum (ty, _, _) ->
        SetType ty
    (* Struct types *)
    | New (id, _) ->
        StructType id
    | Dot (_, id, _) ->
        let decl = IdMap.find id cu.var_decls in
        (match decl.v_type with
        | MapType (_, ty) -> ty
        | _ -> UniversalType)
    (* Other stuff *)
    | Null _ -> UniversalType (*TODO null should have a more precise type, e.g. Loc<T>. *)
    (*| Null _ -> LocType*)
    | ProcCall (id, _, _) ->
        let decl = IdMap.find id cu.proc_decls in
        (match decl.p_returns with
        | [rid] -> 
            let rdecl = IdMap.find rid decl.p_locals in
            rdecl.v_type
        | _ -> UniversalType)
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
    | _ -> UniversalType
  in 
  te e

(** Returns true iff [ty1] is a subtype of [ty2]. *)
let rec is_sub_type ty1 ty2 = 
  match ty1, ty2 with
  | NullType, StructType _
  | StructType _, NullType
  | EmptyType, _ -> true
  | _, UniversalType -> true
  | SetType ty1, SetType ty2 ->
      is_sub_type ty1 ty2
  | MapType (dty1, rty1), MapType (dty2, rty2) ->
      is_sub_type dty2 dty1 && is_sub_type rty1 rty2
  | _ -> ty1 = ty2

let rec match_types ty1 ty2 = 
  match ty1, ty2 with
  | NullType, StructType _
  | StructType _, NullType -> Some ty2
  | UniversalType, _ -> Some ty2
  | _, UniversalType -> Some ty1
  | SetType ty1, SetType ty2 ->
      Util.Opt.map (fun ty -> SetType ty) (match_types ty1 ty2)
  | MapType (dty1, rty1), MapType (dty2, rty2) ->
      (match match_types dty1 dty2, match_types rty1 rty2 with
      | Some dty, Some rty -> Some (MapType (dty, rty))
      | _, _ -> None)
  | ty, tty when ty = tty -> Some ty2
  | _ -> None
